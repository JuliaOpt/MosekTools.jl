# * When we say "variable" we mean an MOI variable and
# * when we say columns, we mean a Mosek variable.
# This is because Mosek variables are numbered 1:n and are columns of the `A`
# matrix while the MOI variables numbering can have holes, i.e. when variables
# are deleted.

###############################################################################
# TASK ########################################################################
###### The `task` field should not be accessed outside this section. ##########

num_columns(task::Mosek.MSKtask) = getnumvar(task)
num_columns(m::MosekModel) = num_columns(m.task)

add_column(task::Mosek.MSKtask) = appendvars(task, 1)
add_column(m::MosekModel) = add_column(m.task)

"""
    function init_columns(task::Mosek.MSKtask, cols::ColumnIndices)

Set the bound to free, i.e. `MSK_BK_FR`, in the internal Mosek task for the
columns cols.

See [`clear_columns`](@ref) which is kind of the reverse operation.
"""
function init_columns(task::Mosek.MSKtask, cols::ColumnIndices)
    # Set each column to a free variable
    N = length(cols.values)
    bnd = zeros(Float64, N)
    putvarboundlist(task, cols.values, fill(MSK_BK_FR, N), bnd, bnd)

    if DEBUG
        for col in cols.values
            putvarname(task, col, "x$col")
        end
    end
    return
end
function init_columns(m::MosekModel, vis::Vector{MOI.VariableIndex})
    init_columns(m.task, columns(m, vis))
end

## Name #######################################################################
###############################################################################
function set_column_name(task::Mosek.MSKtask, col::ColumnIndex, name::String)
    putvarname(task, col.value, name)
end
function set_column_name(m::MosekModel, vi::MOI.VariableIndex, name::String)
    set_column_name(m.task, mosek_index(m, vi), name)
end
column_name(task::Mosek.MSKtask, col::ColumnIndex) = getvarname(task, col.value)
function column_name(m::MosekModel, vi::MOI.VariableIndex)
    column_name(m.task, mosek_index(m, vi))
end
function column_with_name(task::Mosek.MSKtask, name::String)
    asgn, col = getvarnameindex(task, name)
    if iszero(asgn)
        return nothing
    else
        return col
    end
end
column_with_name(m::MosekModel, name::String) = column_with_name(m.task, name)

"""
    function clear_columns(task::Mosek.MSKtask, cols::Vector{Int32})

Delete all coefficients for columns of indices `cols`. Note that the column
is not actually deleted since it will be reused by a new variable when one
is added.

See [`init_columns`](@ref) which is kind of the reverse operation.
"""
function clear_columns(task::Mosek.MSKtask, cols::ColumnIndices)
    N = length(cols.values)
    # Objective: Clear any non-zeros in `c` vector
    putclist(task, cols.values, zeros(Int64, N))

    # Constraints: Clear any non-zeros in columns of `A` matrix
    putacollist(task,
                cols.values,
                zeros(Int64, N),
                zeros(Int64, N),
                Int32[],
                Float64[])

    # Bounds: Fix the variable to zero to make it have very low footprint for
    #         mosek in case `MOI.optimize!` is called before a new variable is
    #         added to reuse this column.
    bnd = zeros(Float64, N)
    putvarboundlist(task, cols.values, fill(MSK_BK_FX, N), bnd, bnd)

    if DEBUG
        for col in cols.values
            # Rename deleted column to help debugging
            putvarname(task, col, "deleted$col")
        end
    end
    return
end
function clear_columns(m::MosekModel, vis::Vector{MOI.VariableIndex})
    clear_columns(m.task, columns(m, vis))
end

###############################################################################
## INDEXING ###################################################################
###############################################################################

function column(m::MosekModel, vi::MOI.VariableIndex)
    @assert iszero(m.x_sd[vi.value].matrix)
    return ColumnIndex(getindex(m.x_block, ref2id(vi)))
end
function columns(m::MosekModel, vis::Vector{MOI.VariableIndex})
    return ColumnIndices(Int32[
        (mosek_index(m, vi)::ColumnIndex).value for vi in vis])
end
function is_scalar(m::MosekModel, vi::MOI.VariableIndex)
    if 1 ≤ vi.value ≤ length(m.x_sd)
        matrix_index = m.x_sd[vi.value]
        if matrix_index.matrix >= 0
            return iszero(matrix_index.matrix)
        end
    end
    throw(MOI.InvalidIndex(vi))
end
function is_matrix(m::MosekModel, vi::MOI.VariableIndex)
    return !is_scalar(m, vi)
end
function mosek_index(m::MosekModel, vi::MOI.VariableIndex)
    if is_scalar(m, vi)
        return column(m, vi)
    else
        return m.x_sd[vi.value]
    end
end

function index_of_column(m::MosekModel, col::Int32)
    id = m.x_block.back[col]
    if iszero(id)
        return nothing
    else
        return MOI.VariableIndex(id)
    end
end

"""
    function allocate_variable(m::MosekModel)

Allocate one variable. If there is a free column (because one variable was
deleted), we use it and don't create any new column, i.e. don't call
`appendvars`. Otherwise, we create new column.

See [`clear_variable`](@ref) which is kind of the reverse operation.
"""
function allocate_variable(m::MosekModel, vi::MOI.VariableIndex)
    numvar = num_columns(m)
    alloced = ensurefree(m.x_block, 1)
    if !iszero(alloced)
        @assert isone(alloced)
        @assert length(m.x_block) == num_columns(m) + 1
        add_column(m)
        @assert length(m.x_block) == num_columns(m)
    end
    allocate_block(m.x_block, 1, vi.value)
end

## Delete #####################################################################
######### Delete variables by clearing the column. The column is reused when ##
######### new variables is added. While there exists a function in the Mosek ##
######### API to delete a column, it is costly and is best avoided.          ##

function throw_if_cannot_delete(m::MosekModel, vi::MOI.VariableIndex)
    if !allocated(m.x_block, ref2id(vi))
        @assert m.x_sd[ref2id(vi)].matrix == -1
        throw(MOI.InvalidIndex(vi))
    end
    if is_scalar(m, vi)
        col = column(m, vi)
        for S in [MOI.LessThan{Float64}, MOI.GreaterThan{Float64},
                  MOI.EqualTo{Float64}, MOI.Interval{Float64},
                  MOI.Integer]
            if has_flag(m, vi, S)
                MOI.delete(m, MOI.ConstraintIndex{MOI.SingleVariable, S}(vi.value))
            end
        end
        # All bounds have been removed so there can only be not constraint left
        # on the variable or a `VectorOfVariable`-in-`VectorCone` constraint.
        if has_flag(m, vi, VectorCone)
            throw(MOI.DeleteNotAllowed("Cannot delete variable $vi as it is involved in a `VectorOfVariables` constraint."))
        end
    end
end

"""
    clear_variable(m::MosekModel, vi::MOI.VariableIndex)

Delete the `vi` variable (without actually doing any change to the internal
Mosek solver) to free the corresponding column for reuse by another variable.

See [`allocate_variable`](@ref) which is kind of the reverse operation.
"""
function clear_variable(m::MosekModel, vi::MOI.VariableIndex)
    deleteblock(m.x_block, ref2id(vi))
end

###############################################################################
# MOI #########################################################################
###############################################################################

## Add ########################################################################
###############################################################################

function new_variable_index(m::MosekModel, matrix_index::MatrixIndex)
    id = create_block(m.x_block, 1)
    push!(m.x_constraints, 0x0)
    push!(m.x_sd, matrix_index)
    push!(m.variable_to_vector_constraint_id, 0)
    return MOI.VariableIndex(id)
end

function MOI.add_variable(m::MosekModel)
    vi = new_variable_index(m, MatrixIndex(0, 0, 0))
    allocate_variable(m, vi)
    init_columns(m, [vi])
    return vi
end

function MOI.add_variables(m::MosekModel, n::Int)
    @assert n ≥ 0
    return MOI.VariableIndex[MOI.add_variable(m) for i in 1:n]
end

## Delete #####################################################################
###############################################################################
function MOI.is_valid(model::MosekModel, vi::MOI.VariableIndex)
    return allocated(model.x_block, ref2id(vi))
end
function delete_vector_of_variables_constraint(m::MosekModel, vis::Vector{MOI.VariableIndex})
    i = first(vis).value
    id = m.variable_to_vector_constraint_id[i]
    if id > 0
        S = type_cone(getconeinfo(m.task, id)[1])
        ci = MOI.ConstraintIndex{MOI.VectorOfVariables, S}(i)
        if MOI.is_valid(m, ci) && vis == MOI.get(m, MOI.ConstraintFunction(), ci).variables
            MOI.delete(m, ci)
        end
    end
end
function MOI.delete(m::MosekModel, vis::Vector{MOI.VariableIndex})
    for vi in vis
        throw_if_cannot_delete(m, vi)
    end
    delete_vector_of_variables_constraint(m, vis)
    for vi in vis
        MOI.delete(m, vi)
    end
#    clear_columns(m, vis)
#    for vi in vis
#        clear_variable(m, vi)
#    end
end
function MOI.delete(m::MosekModel, vi::MOI.VariableIndex)
    throw_if_cannot_delete(m, vi)
    delete_vector_of_variables_constraint(m, [vi])
    if !iszero(m.variable_to_vector_constraint_id[vi.value])
        MOIU.throw_delete_variable_in_vov(vi)
    end
    clear_columns(m, [vi])
    clear_variable(m, vi)
    m.x_sd[vi.value] = MatrixIndex(-1, 0, 0)
    return
end

## List #######################################################################
###############################################################################
MOI.get(m::MosekModel, ::MOI.NumberOfVariables) = num_allocated(m.x_block)
function MOI.get(m::MosekModel, ::MOI.ListOfVariableIndices)
    ids = allocatedlist(m.x_block)
    return MOI.VariableIndex[MOI.VariableIndex(vid) for vid in ids]
end
function MOI.get(m::MosekModel, ::MOI.ListOfVariableAttributesSet)
    set = MOI.AbstractVariableAttribute[]
    if m.has_variable_names
        push!(set, MOI.VariableName())
    end
    # TODO add VariablePrimalStart when get is implemented on it
    return set
end

## Name #######################################################################
###############################################################################
MOI.supports(::MosekModel, ::MOI.VariableName, ::Type{MOI.VariableIndex}) = true
function MOI.set(m::MosekModel, ::MOI.VariableName, vi::MOI.VariableIndex,
                 name::String)
    m.has_variable_names = true
    set_column_name(m, vi, name)
end
function MOI.get(m::MosekModel, ::MOI.VariableName, vi::MOI.VariableIndex)
    return column_name(m, vi)
end
function MOI.get(m::MosekModel, ::Type{MOI.VariableIndex}, name::String)
    col = column_with_name(m, name)
    if col === nothing
        return nothing
    else
        return index_of_column(m, col)
    end
end
