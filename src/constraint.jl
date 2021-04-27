###############################################################################
# TASK ########################################################################
###### The `task` field should not be accessed outside this section. ##########

## Affine Constraints #########################################################
##################### lc ≤ Ax ≤ uc ############################################

function allocate_afe(m::MosekModel, N::Int)
    numafe = getnumcon(m.task)

    allocd,afeidxs = allocate(m.afes,N)
    if allocd > 0
        Mosek.appendafes(m.task,allocd)
    end
    afeidxs
end

function allocateconstraints(m::MosekModel, N::Int)
    numcon = getnumcon(m.task)
    alloced = ensurefree(m.c_block,N)
    id = newblock(m.c_block, N)

    if alloced > 0
          appendcons(m.task, alloced)
    end
    return id
end

function getconboundlist(t::Mosek.Task, subj::Vector{Int32})
    n = length(subj)
    bk = Vector{Boundkey}(undef,n)
    bl = Vector{Float64}(undef,n)
    bu = Vector{Float64}(undef,n)
    for i in 1:n
        bki,bli,bui = getconbound(t,subj[i])
        bk[i] = bki
        bl[i] = bli
        bu[i] = bui
    end
    bk,bl,bu
end

# `putbaraij` and `putbarcj` need the whole matrix as a sum of sparse mat at once
function split_scalar_matrix(m::MosekModel, terms::Vector{MOI.ScalarAffineTerm{Float64}},
                             set_sd::Function)
    cols    = Int32[]
    values  = Float64[]
    sd_row  = Vector{Int32}[Int32[] for i in 1:length(m.sd_dim)]
    sd_col  = Vector{Int32}[Int32[] for i in 1:length(m.sd_dim)]
    sd_coef = Vector{Float64}[Float64[] for i in 1:length(m.sd_dim)]
    function add(col::ColumnIndex, coefficient::Float64)
	push!(cols, col.value)
	push!(values, coefficient)
    end
    function add(mat::MatrixIndex, coefficient::Float64)
        coef = mat.row == mat.column ? coefficient : coefficient / 2
        push!(sd_row[mat.matrix], mat.row)
        push!(sd_col[mat.matrix], mat.column)
        push!(sd_coef[mat.matrix], coef)
    end
    for term in terms
        add(mosek_index(m, term.variable_index), term.coefficient)
    end
    for j in 1:length(m.sd_dim)
        if !isempty(sd_row[j])
            id = appendsparsesymmat(m.task, m.sd_dim[j], sd_row[j],
                                    sd_col[j], sd_coef[j])
            set_sd(j, [id], [1.0])
        end
    end
    return cols, values
end

function set_row(task::Mosek.MSKtask, row::Int32, cols::ColumnIndices,
                 values::Vector{Float64})
    putarow(task, row, cols.values, values)
end
function set_row(m::MosekModel, row::Int32,
                 terms::Vector{MOI.ScalarAffineTerm{Float64}})
    cols, values = split_scalar_matrix(m, terms,
        (j, ids, coefs) -> putbaraij(m.task, row, j, ids, coefs))
    set_row(m.task, row, ColumnIndices(cols), values)
end


function set_coefficients(task::Mosek.MSKtask, rows::Vector{Int32},
                          cols::ColumnIndices, values::Vector{Float64})
    putaijlist(task, rows, cols.values, values)
end

function set_coefficients(task::Mosek.MSKtask, rows::Vector{Int32},
                          col::ColumnIndex, values::Vector{Float64})
    n = length(rows)
    @assert n == length(values)
    set_coefficient(task, rows, ColumnIndices(fill(col.value, n)), values)
end
function set_coefficients(m::MosekModel, rows::Vector{Int32},
                          vi::MOI.VariableIndex, values::Vector{Float64})
    set_coefficient(m.task, rows, mosek_index(m, vi), values)
end

function set_coefficient(task::Mosek.MSKtask, row::Int32, col::ColumnIndex,
                         value::Float64)
    putaij(task, row, col.value, value)
end
function set_coefficient(m::MosekModel, row::Int32, vi::MOI.VariableIndex,
                         value::Float64)
    set_coefficient(m.task, row, mosek_index(m, vi), value)
end

bound_key(::Type{MOI.GreaterThan{Float64}}) = MSK_BK_LO
bound_key(::Type{MOI.LessThan{Float64}})    = MSK_BK_UP
bound_key(::Type{MOI.EqualTo{Float64}})     = MSK_BK_FX
bound_key(::Type{MOI.Interval{Float64}})    = MSK_BK_RA



add_bound(m::MosekModel, row::Int32, dom::MOI.GreaterThan{Float64}) = putconbound(m.task, row, bound_key(typeof(dom)), dom.lower, dom.lower)
add_bound(m::MosekModel, row::Int32, dom::MOI.LessThan{Float64})    = putconbound(m.task, row, bound_key(typeof(dom)), dom.upper, dom.upper)
add_bound(m::MosekModel, row::Int32, dom::MOI.EqualTo{Float64})     = putconbound(m.task, row, bound_key(typeof(dom)), dom.value, dom.value)
function add_bound(m::MosekModel, row::Int32, dom::MOI.Interval{Float64})
    bl = dom.lower
    bu = dom.upper
    bk = bound_key(typeof(dom))
    if bl < 0 && isinf(bl)
        if bu > 0 && isinf(bu)
            bk = MSK_BK_FR
        else
            bk = MSK_BK_UP
        end
    elseif bu > 0 && isinf(bu)
        bk = MSK_BK_LO
    end

    putconbound(m.task, row, bk,bl,bu)
end

function bounds_to_set(::Type{S}, bk, bl, bu) where S
    if S == MOI.GreaterThan{Float64}
        return S(bl)
    elseif S == MOI.LessThan{Float64}
        return S(bu)
    elseif S == MOI.EqualTo{Float64}
        @assert bl == bu
        return S(bu)
    else
        @assert S == MOI.Interval{Float64}
        return S(bl, bu)
    end
end
function get_bound(m::MosekModel,
                   ci::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}, S}) where{S}
    bounds_to_set(S, getconbound(m.task, row(m, ci))...)
end

## Variable Constraints #######################################################
####################### lx ≤ x ≤ u ############################################
#######################      x ∈ K ############################################

function getvarboundlist(t::Mosek.Task, subj::Vector{Int32})
    n = length(subj)
    bk = Vector{Boundkey}(undef,n)
    bl = Vector{Float64}(undef,n)
    bu = Vector{Float64}(undef,n)
    for i in 1:n
        bki,bli,bui = getvarbound(t, subj[i])
        bk[i] = bki
        bl[i] = bli
        bu[i] = bui
    end
    bk,bl,bu
end


function delete_variable_constraint(m::MosekModel, col::ColumnIndex,
                                    ::Type{<:Union{MOI.Interval, MOI.EqualTo}})
    putvarbound(m.task, col.value, MSK_BK_FR, 0.0, 0.0)
end
function delete_variable_constraint(m::MosekModel, col::ColumnIndex,
                                    ::Type{MOI.Integer})
    putvartype(m.task, col.value, MSK_VAR_TYPE_CONT)
end
function delete_variable_constraint(m::MosekModel, col::ColumnIndex,
                                    ::Type{MOI.LessThan{Float64}})
    bk, lo, up = getvarbound(m.task, col.value)
    if bk == MSK_BK_UP
        bk = MSK_BK_FR
    else
        @assert bk == MSK_BK_RA
        bk = MSK_BK_LO
    end
    putvarbound(m.task, col.value, bk, lo, 0.0)
end
function delete_variable_constraint(m::MosekModel, col::ColumnIndex,
                                    ::Type{MOI.GreaterThan{Float64}})
    bk, lo, up = getvarbound(m.task, col.value)
    if bk == MSK_BK_LO
        bk = MSK_BK_FR
    else
        @assert bk == MSK_BK_RA
        bk = MSK_BK_UP
    end
    putvarbound(m.task, col.value, bk, 0.0, up)
end
function add_variable_constraint(m::MosekModel, col::ColumnIndex, dom::MOI.Interval)
    putvarbound(m.task, col.value, MSK_BK_RA, dom.lower, dom.upper)
end
function add_variable_constraint(m::MosekModel, col::ColumnIndex, dom::MOI.EqualTo)
    putvarbound(m.task, col.value, MSK_BK_FX, dom.value, dom.value)
end
function add_variable_constraint(m::MosekModel, col::ColumnIndex, ::MOI.Integer)
    putvartype(m.task, col.value, MSK_VAR_TYPE_INT)
end
function add_variable_constraint(m::MosekModel, col::ColumnIndex, dom::MOI.LessThan)
    bk, lo, up = getvarbound(m.task, col.value)
    if bk == MSK_BK_FR
        bk = MSK_BK_UP
    else
        @assert bk == MSK_BK_LO
        bk = MSK_BK_RA
    end
    putvarbound(m.task, col.value, bk, lo, dom.upper)
end
function add_variable_constraint(m::MosekModel, col::ColumnIndex,
                                 dom::MOI.GreaterThan)
    bk, lo, up = getvarbound(m.task, col.value)
    if bk == MSK_BK_FR
        bk = MSK_BK_LO
    else
        @assert bk == MSK_BK_UP
        bk = MSK_BK_RA
    end
    putvarbound(m.task, col.value, bk, dom.lower, up)
end
function get_variable_constraint(m::MosekModel,
                                 col::ColumnIndex,
                                 ci::MOI.ConstraintIndex{MOI.SingleVariable, S}) where S
    return bounds_to_set(S, getvarbound(m.task, col.value)...)
end
function get_variable_constraint(m::MosekModel, vi::MOI.VariableIndex,
                                 ci::MOI.ConstraintIndex)
    return get_variable_constraint(m, mosek_index(m, vi), ci)
end

cone_parameter(dom :: MOI.PowerCone{Float64})     = dom.exponent
cone_parameter(dom :: MOI.DualPowerCone{Float64}) = dom.exponent
cone_parameter(dom :: C) where C <: MOI.AbstractSet = 0.0

function add_cone(m::MosekModel, cols::ColumnIndices, set)
    appendcone(m.task, cone_type(typeof(set)), cone_parameter(set), cols.values)
    id = getnumcone(m.task)
    if DEBUG
        putconename(m.task, id, "$id")
    end
    return id
end

## Name #######################################################################
###############################################################################

function set_row_name(task::Mosek.MSKtask, row::Int32, name::String)
    putconname(task, row, name)
end

function set_row_name(m::MosekModel,
                      c::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}},
                      name::AbstractString)
    set_row_name(m.task, row(m, c), name)
end
function set_row_name(m::MosekModel, c::MOI.ConstraintIndex,
                      name::AbstractString)
    # Fallback for `SingleVariable` and `VectorOfVariables`.
    m.con_to_name[c] = name
end

function delete_name(m::MosekModel, ci::MOI.ConstraintIndex)
    name = MOI.get(m, MOI.ConstraintName(), ci)
    if !isempty(name)
        cis = m.constrnames[name]
        deleteat!(cis, findfirst(isequal(ci), cis))
    end
end

###############################################################################
# INDEXING ####################################################################
###############################################################################

function row(m::MosekModel,
             c::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}})::Int32
    return getindex(m.c_block, c.value)
end
function columns(m::MosekModel, ci::MOI.ConstraintIndex{MOI.VectorOfVariables})
    coneidx = cone_id(m, ci)
    if coneidx < 1 || coneidx > getnumcone(m.task)
        throw(MOI.InvalidIndex(ci))
    end
    return ColumnIndices(getcone(m.task, coneidx)[4])
end

const VectorCone = Union{MOI.SecondOrderCone,
                         MOI.RotatedSecondOrderCone,
                         MOI.PowerCone,
                         MOI.DualPowerCone,
                         MOI.ExponentialCone,
                         MOI.DualExponentialCone}

# Two `SingleVariable`-in-`S` cannot be set to the same variable if
# the two constraints
# * both set a lower bound, or
# * both set an upper bound, or
# * both set it to integer.
# The `incompatible_mask` are computed according to these rules.
flag(::Type{MOI.EqualTo{Float64}}) = 0x1
incompatible_mask(::Type{MOI.EqualTo{Float64}}) = 0x2f
flag(::Type{MOI.GreaterThan{Float64}}) = 0x2
incompatible_mask(::Type{MOI.GreaterThan{Float64}}) = 0x2b
flag(::Type{MOI.LessThan{Float64}}) = 0x4
incompatible_mask(::Type{MOI.LessThan{Float64}}) = 0x2d
flag(::Type{MOI.Interval{Float64}}) = 0x8
incompatible_mask(::Type{MOI.Interval{Float64}}) = 0x2f
flag(::Type{MOI.Integer}) = 0x10
incompatible_mask(::Type{MOI.Integer}) = 0x30
flag(::Type{<:VectorCone}) = 0x40
incompatible_mask(::Type{<:VectorCone}) = 0x40

function set_flag(model::MosekModel, vi::MOI.VariableIndex, S::Type)
    model.x_constraints[vi.value] |= flag(S)
end
function unset_flag(model::MosekModel, vi::MOI.VariableIndex, S::Type)
    model.x_constraints[vi.value] &= ~flag(S)
end
function has_flag(model::MosekModel, vi::MOI.VariableIndex, S::Type)
    return !iszero(model.x_constraints[vi.value] & flag(S))
end

###############################################################################
# MOI #########################################################################
###############################################################################

const ScalarLinearDomain = Union{MOI.LessThan{Float64},
                                 MOI.GreaterThan{Float64},
                                 MOI.EqualTo{Float64},
                                 MOI.Interval{Float64}}

## Add ########################################################################
###############################################################################

MOI.supports_constraint(::MosekModel, ::Type{<:Union{MOI.SingleVariable, MOI.ScalarAffineFunction}}, ::Type{<:ScalarLinearDomain}) = true
MOI.supports_constraint(::MosekModel, ::Type{MOI.VectorOfVariables}, ::Type{<:VectorCone}) = true
MOI.supports_constraint(::MosekModel, ::Type{MOI.SingleVariable}, ::Type{<:MOI.Integer}) = true
MOI.supports_add_constrained_variables(::MosekModel, ::Type{MOI.PositiveSemidefiniteConeTriangle}) = true

## Affine Constraints #########################################################
##################### lc ≤ Ax ≤ uc ############################################

function MOI.add_constraint(m  ::MosekModel,
                            axb::MOI.ScalarAffineFunction{Float64},
                            dom::D) where{D <: MOI.AbstractScalarSet}
    if !iszero(axb.constant)
        throw(MOI.ScalarFunctionConstantNotZero{Float64, typeof(axb), D}(axb.constant))
    end

    # Duplicate indices not supported
    N = 1
    axb     = MOIU.canonical(axb)

    conid = allocateconstraints(m, N)
    ci = MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}, D}(conid)
    r = row(m, ci)
    set_row(m, r, axb.terms)

    add_bound(m, r, dom)

    return ci
end

# function MOI.add_constraint(m ::MosekModel,
#                             axb::MOI.VectorAffineFunction{Float64},
#                             dom::D) where {D <: MOI.AbstractVectorSet}
# end
## Variable Constraints #######################################################
####################### lx ≤ x ≤ u ############################################
#######################      x ∈ K ############################################

# We allow following. Each variable can have
# - at most most upper and one lower bound
# - belong to at most one non-semidefinite cone
# - any number of semidefinite cones, which are implemented as ordinary constraints
# This is when things get a bit funky; By default a variable has no
# bounds, i.e. "free". Adding a `GreaterThan`
# constraint causes it to have a defined lower bound but no upper
# bound, allowing a `LessThan` constraint to be
# added later. Adding a `Interval` constraint defines both upper and
# lower bounds.

cone_type(::Type{MOI.ExponentialCone})        = MSK_CT_PEXP
cone_type(::Type{MOI.DualExponentialCone})    = MSK_CT_DEXP
cone_type(::Type{MOI.PowerCone{Float64}})     = MSK_CT_PPOW
cone_type(::Type{MOI.DualPowerCone{Float64}}) = MSK_CT_DPOW
cone_type(::Type{MOI.SecondOrderCone})        = MSK_CT_QUAD
cone_type(::Type{MOI.RotatedSecondOrderCone}) = MSK_CT_RQUAD

function MOI.add_constraint(
    m   :: MosekModel,
    xs  :: MOI.SingleVariable,
    dom :: D) where{D <: MOI.AbstractScalarSet}

    msk_idx = mosek_index(m, xs.variable)
    if !(msk_idx isa ColumnIndex)
        error("Cannot add $D constraint on a matrix variable")
    end

    if !iszero(incompatible_mask(D) & m.x_constraints[xs.variable.value])
        error("Cannot put multiple bound sets of the same type on a variable")
    end

    set_flag(m, xs.variable, D)

    add_variable_constraint(m, msk_idx, dom)

    return MOI.ConstraintIndex{MOI.SingleVariable, D}(xs.variable.value)
end

function MOI.add_constraint(m::MosekModel,
                            xs::MOI.VectorOfVariables,
                            dom::D) where {D<:VectorCone}
    if any(vi -> is_matrix(m, vi), xs.variables)
        error("Cannot add $D constraint on a matrix variable")
    end
    cols = ColumnIndices(reorder(columns(m, xs.variables).values, D))

    if !all(vi -> iszero(incompatible_mask(D) & m.x_constraints[vi.value]), xs.variables)
        error("Cannot multiple bound sets of the same type to a variable")
    end

    N   = MOI.dimension(dom)
    id  = add_cone(m, cols, dom)
    idx = first(xs.variables).value
    for vi in xs.variables
        m.variable_to_vector_constraint_id[vi.value] = -idx
    end
    m.variable_to_vector_constraint_id[idx] = id

    ci = MOI.ConstraintIndex{MOI.VectorOfVariables, D}(idx)
    return ci
end

append_domain(m::MosekModel, dom::MOI.Reals)                  = Mosek.appendrdomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.Zeros)                  = Mosek.appendrzerodomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.Nonnegatives)           = Mosek.appendrplusdomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.Nonpositives)           = Mosek.appendrminusdomain(m.task,Int64(dom.dimension))
#append_domain(m::MosekModel, dom::MOI.NormInfinityCone)       = Mosek.appendinfnormconedomain(m.task,Int64(dom.dimension))
#append_domain(m::MosekModel, dom::MOI.NormOneCone)            = Mosek.appendonenormconedomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.SecondOrderCone)        = Mosek.appendquadconedomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.RotatedSecondOrderCone) = Mosek.appendrquadconedomain(m.task,Int64(dom.dimension))
#append_domain(m::MosekModel, dom::MOI.GeometricMeanCone)      = Mosek.appendprimalgeomeanconedomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.ExponentialCone)        = Mosek.appendprimalexpconedomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.DualExponentialCone)    = Mosek.appenddualexpconedomain(m.task,Int64(dom.dimension))
append_domain(m::MosekModel, dom::MOI.PowerCone)              = Mosek.appendprimalpowerconedomain(m.task,3,2,Float64[dom.exponent,1.0-dom.exponent])
append_domain(m::MosekModel, dom::MOI.DualPowerCone)          = Mosek.appendprimalpowerconedomain(m.task,3,2,Float64[dom.exponent,1.0-dom.exponent])
append_domain(m::MosekModel, dom::MOI.PositiveSemidefiniteConeTriangle) = Mosek.appendpsdconedomain(m.task,Int64(dom.dimension))

#MOI.ExponentialCone
#MOI.DualExponentialCone
#MOI.PositiveSemidefiniteConeTriangle
index_julia_to_mosek(afeidxs::Vector{Int64},dom::D) where {D<:ACCUntransformedVectorDomain} = afeidxs
index_julia_to_mosek(afeidxs::Vector{Int64},dom::MOI.ExponentialCone)     = Int64[afeidxs[3],afeidxs[2],afeidxs[1]]
index_julia_to_mosek(afeidxs::Vector{Int64},dom::MOI.DualExponentialCone) = Int64[afeidxs[3],afeidxs[2],afeidxs[1]]
function index_julia_to_mosek(afeidxs::Vector{Int64},dom::MOI.PositiveSemidefiniteConeTriangle)
    d = dom.side_dimension
    Int64[ afeidxs[i*(d+1)/2+j] for j in 1:d for i in j:d]
end


function set_afe_rows(m::MosekModel,
                      afeidxs::Vector{Int64},
                      axb::MOI.VectorAffineFunction{Float64})
    terms  = axb.terms
    consts = axb.constants

    nrows = length(afeidxs)
    N = length(terms)

    subi  = Vector{Int32}(undef,N)
    subj  = Vector{Int32}(undef,N)
    subii = Vector{Int32}(undef,N)
    subjj = Vector{Int32}(undef,N)
    cof   = Vector{Float64}(undef,N)

    i    = 0
    nlin = 0

    for term in axb.terms
        vi = term.scalar_term.variable_index
        if 1 <= vi.value <= length(m.x_sd)
            matrix_index = m.x_sd[vi.value]
            i += 1
            subi[i] = term.output_index
            if matrix_index.matrix == 0
                nlin += 1
                subj[i] = 0
                subii[i] = 0
                subjj[i] = getindex(m.x_block, ref2id(vi))
                cof[i]  = term.scalar_term.coefficient
            else
                subj[i] = matrix_index.matrix
                subii[i] = matrix_index.row
                subjj[i] = matrix_index.column
                cof[i]  = term.scalar_term.coefficient
            end
        end
    end

    perm = Int[1:N...]
    sort(perm,by=i->(subi[i],subj[i],subii[i],subjj[i]))

    psubi  = view(subi,perm)
    psubj  = view(subj,perm)
    psubii = view(subii,perm)
    psubjj = view(subjj,perm)
    pcof   = view(cof,perm)

    ptrrow = Vector{Int64}(undef,nrows)
    nzrow  = Vector{Int32}(undef,nrows)
    ptrrow = Vector{Int64}(undef,nrows)
    let p = 1
        for i in 1:nrows
            ptrrow[i] = p
            ptrb = p
            ptrrow[i] = p
            while p <= nlin && psubi[p] == i  p += 1 end
            nzrow[i] = p-ptrb
        end
    end

    Mosek.putafefrowlist(m.task,afeidxs,nzrow,ptrrow,psubjj[1:nlin],pcof[1:nlin])
    Mosek.putafeglist(m.task,afeidxs,consts)

    if N > nlin # psd terms
        let p = nlin+1
            while p <= N
                i = psubi[p]
                j = psubj[p]
                ptrb = p
                p += 1
                while i == psubi[p] && j == psubj[p]  p += 1 end
                midx = Mosek.appendsparsesymmat(m.task,m.sd_dim[i],psubii[ptrb:p-1],psubjj[ptrb:p-1],pcof[ptrb:p-1])
                Mosek.putafebarfentry(m.task,i,j,[midx],[1.0])
            end
        end
    end
end

function clear_afe_rows(m::MosekModel,
                        afeidxs::Vector{Int64})
    emptyafebarfrowlist(m.task,afeidxs)
    N = length(afeidxs)
    rownz = zeros(Int32,N)
    rowptr = zeros(Int64,N)
    putafefrowlist(m.task,afeidxs,zeros(Int32,N),zeros(Int64,N),Int32[],Float64[])
    putafeglist(m.task,afeidxs,zeros(Float64,N))
end

if Mosek.getversion() >= (10,0,0)
MOI.supports_constraint(mosek::MosekModel,::Type{MOI.VectorAffineFunction{Float64}},::Type{<:ACCVectorDomain}) = true

function MOI.add_constraint(m::MosekModel,
                            axb::MOI.VectorAffineFunction{Float64},
                            dom::D) where{D<:ACCVectorDomain}
    N = MOI.dimension(dom)
    afeidxs = allocate_afe(m,N)
    domidx = append_domain(m,dom)

    axb = MOIU.canonical(axb)
    set_afe_rows(m,afeidxs,axb)

    accid = Mosek.getnumacc(m.task)+1
    Mosek.appendacc(m.task,
                    domidx,
                    index_julia_to_mosek(afeidxs,dom),
                    zeros(Float64,N))

    ci = MOI.ConstraintIndex{MOI.VectorAffineFunction{Float64},D}(accid)
    return ci
end
end  # if Mosek.getversion() >= 10

function cone_id(model::MosekModel, ci::MOI.ConstraintIndex{MOI.VectorOfVariables})
    return model.variable_to_vector_constraint_id[ci.value]
end

################################################################################
################################################################################

function MOI.add_constrained_variables(
    m  ::MosekModel,
    dom::MOI.PositiveSemidefiniteConeTriangle )
    N = dom.side_dimension
    if N < 2
        error("Invalid dimension for semidefinite constraint, got $N which is ",
              "smaller than the minimum dimension 2.")
    end
    appendbarvars(m.task, [Int32(N)])
    push!(m.sd_dim, N)
    id = length(m.sd_dim)
    vis = [new_variable_index(m, MatrixIndex(id, i, j)) for i in 1:N for j in 1:i]
    con_idx = MOI.ConstraintIndex{MOI.VectorOfVariables, MOI.PositiveSemidefiniteConeTriangle}(id)
    return vis, con_idx
end

## Get ########################################################################
###############################################################################

_variable(ci::MOI.ConstraintIndex{MOI.SingleVariable}) = MOI.VariableIndex(ci.value)
function MOI.get(m::MosekModel, ::MOI.ConstraintFunction,
                 ci::MOI.ConstraintIndex{MOI.SingleVariable}) where S <: ScalarLinearDomain
    MOI.throw_if_not_valid(m, ci)
    return MOI.SingleVariable(_variable(ci))
end
function MOI.get(m::MosekModel, ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.SingleVariable, S}) where S <: MOI.Integer
    MOI.throw_if_not_valid(m, ci)
    return S()
end
function MOI.get(m::MosekModel, ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.SingleVariable, S}) where S <: ScalarLinearDomain
    MOI.throw_if_not_valid(m, ci)
    sv = MOI.get(m, MOI.ConstraintFunction(), ci)
    return get_variable_constraint(m, sv.variable, ci)
end

function MOI.get(m::MosekModel, ::MOI.ConstraintFunction,
                 ci::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64},
                                         <:ScalarLinearDomain})
    MOI.throw_if_not_valid(m, ci)
    nnz, cols, vals = getarow(m.task, row(m, ci))
    @assert nnz == length(cols) == length(vals)
    terms = MOI.ScalarAffineTerm{Float64}[
        MOI.ScalarAffineTerm(vals[i], index_of_column(m, cols[i])) for i in 1:nnz]
    # TODO add matrix terms
    return MOI.ScalarAffineFunction(terms, 0.0)
end
function MOI.get(m::MosekModel, ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}})
    MOI.throw_if_not_valid(m, ci)
    return get_bound(m, ci)
end
function MOI.get(m::MosekModel, ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.VectorAffineFunction{Float64}})
    accidx = ci.value
    domidx = getaccdomain(m.task,accidx)
    domsize = getdomainn(m.task,domidx)
    domtp   = getdomaintype(m.task,domidx)
    set = ( if     domtp == Mosek.MSK_DOMAIN_R                     MOI.Reals(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_RZERO                 MOI.Zeros(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_RPLUS                 MOI.Nonnegatives(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_RMINUS                MOI.Nonpositives(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_QUADRATIC_CONE        MOI.SecondOrderCone(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_RQUADRATIC_CONE       MOI.RotatedSecondOrderCone(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_PRIMAL_EXP_CONE       MOI.ExponentialCone()
            elseif domtp == Mosek.MSK_DOMAIN_DUAL_EXP_CONE         MOI.DualExponentialCone()
            elseif domtp == Mosek.MSK_DOMAIN_PRIMAL_POWER_CONE     MOI.PowerCone()
            elseif domtp == Mosek.MSK_DOMAIN_DUAL_POWER_CONE       MOI.DualPowerCone()
            elseif domtp == Mosek.MSK_DOMAIN_PRIMAL_GEO_MEAN_CONE  MOI.GeometricMeanCone(domsize)
            #elseif domtp == Mosek.MSK_DOMAIN_DUAL_GEO_MEAN_CONE    MOI.GeometricMeanCone(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_INF_NORM_CONE         MOI.NormInfinityCone(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_ONE_NORM_CONE         MOI.NormOneCone(domsize)
            elseif domtp == Mosek.MSK_DOMAIN_PSD_CONE              MOI.PositiveSemidefiniteConeTriangle(domsize)
            else error("Unsupported cone type")
            end )
    return set
end

function MOI.get(m::MosekModel, ::MOI.ConstraintFunction,
                 ci::MOI.ConstraintIndex{MOI.VectorOfVariables, S}) where S <: VectorCone
    return MOI.VectorOfVariables([
        index_of_column(m, col) for col in reorder(columns(m, ci).values, S)
    ])
end

function MOI.get(m::MosekModel, ::MOI.ConstraintFunction, ci::MOI.ConstraintIndex{MOI.VectorAffineFunction{Float64}, <:ACCVectorDomain})
    accid = ci.value
    afeidxs = getaccafeidxlist(m.task,accid)
    N = length(afeidxs)

    terms = MOI.VectorAffineTerm[]
    b = Float64[ getafeg(m.task,i) for i in 1:N ]

    for i in 1:N
        (_,subj,cof) = getafefrow(m.task,i)
        M = length(subj)
        for j in 1:M
            push!(terms,MOI.VectorAffineTerm(i,MOI.ScalarAffineTerm(cof[j],index_of_column(m,subj[j]))))
        end
    end
    # TODO add matrix terms
    return MOI.VectorAffineFunction{Float64}(terms, b)
end

function type_cone(ct)
    if ct == MSK_CT_PEXP
        return MOI.ExponentialCone
    elseif ct == MSK_CT_DEXP
        return MOI.DualExponentialCone
    elseif ct == MSK_CT_PPOW
        return MOI.PowerCone{Float64}
    elseif ct == MSK_CT_DPOW
        return MOI.DualPowerCone{Float64}
    elseif ct == MSK_CT_QUAD
        return MOI.SecondOrderCone
    elseif ct == MSK_CT_RQUAD
        return MOI.RotatedSecondOrderCone
    else
        error("Unrecognized Mosek cone type `$ct`.")
    end
end
cone(::Type{MOI.ExponentialCone}, conepar, nummem) = MOI.ExponentialCone()
cone(::Type{MOI.DualExponentialCone}, conepar, nummem) = MOI.DualExponentialCone()
cone(::Type{MOI.PowerCone{Float64}}, conepar, nummem) = MOI.PowerCone(conepar)
cone(::Type{MOI.DualPowerCone{Float64}}, conepar, nummem) = MOI.DualPowerCone(conepar)
cone(::Type{MOI.SecondOrderCone}, conepar, nummem) = MOI.SecondOrderCone(nummem)
cone(::Type{MOI.RotatedSecondOrderCone}, conepar, nummem) = MOI.RotatedSecondOrderCone(nummem)
function MOI.get(m::MosekModel, ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.VectorOfVariables, <:VectorCone})
    MOI.throw_if_not_valid(m, ci)
    ct, conepar, nummem = getconeinfo(m.task, cone_id(m, ci))
    return cone(type_cone(ct), conepar, nummem)
end

## Modify #####################################################################
###############################################################################

### SET
chgbound(bl::Float64,bu::Float64,k::Float64,dom :: MOI.LessThan{Float64})    = bl,dom.upper-k
chgbound(bl::Float64,bu::Float64,k::Float64,dom :: MOI.GreaterThan{Float64}) = dom.lower-k,bu
chgbound(bl::Float64,bu::Float64,k::Float64,dom :: MOI.EqualTo{Float64})     = dom.value-k,dom.value-k
chgbound(bl::Float64,bu::Float64,k::Float64,dom :: MOI.Interval{Float64})    = dom.lower-k,dom.upper-k

function MOI.set(m::MosekModel,
                 ::MOI.ConstraintSet,
                 ci::MOI.ConstraintIndex{MOI.SingleVariable,D},
                 dom::D) where D<:ScalarLinearDomain
    col = column(m, _variable(ci))
    bk, bl, bu = getvarbound(m.task, col.value)
    bl, bu = chgbound(bl, bu, 0.0, dom)
    putvarbound(m.task, col.value, bk, bl, bu)
end


function MOI.set(m::MosekModel,
                 ::MOI.ConstraintSet,
                 cref::MOI.ConstraintIndex{<:MOI.ScalarAffineFunction,D},
                 dom::D) where D <: ScalarLinearDomain
    cid = ref2id(cref)
    i = getindex(m.c_block, cid) # since we are in a scalar domain
    bk, bl, bu = getconbound(m.task, i)
    bl, bu = chgbound(bl, bu, 0.0, dom)
    putconbound(m.task, i, bk, bl, bu)
end


### MODIFY
function MOI.modify(m   ::MosekModel,
                    c   ::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64},D},
                    func::MOI.ScalarConstantChange{Float64}) where {D <: MOI.AbstractSet}
    if !iszero(func.new_constant)
        throw(MOI.ScalarFunctionConstantNotZero{Float64, MOI.ScalarAffineFunction{Float64}, D}(func.new_constant))
    end
end

function MOI.modify(m   ::MosekModel,
                    c   ::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}},
                    func::MOI.ScalarCoefficientChange{Float64})
    set_coefficient(m, row(m, c), func.variable, func.new_coefficient)
end

### TRANSFORM
function MOI.transform(m::MosekModel,
                       cref::MOI.ConstraintIndex{F,D},
                       newdom::D) where {F <: MOI.AbstractFunction,
                                         D <: MOI.AbstractSet}
    MOI.modify(m,cref,newdom)
    return cref
end

function MOI.transform(m::MosekModel,
                       cref::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64},D1},
                       newdom::D2) where {D1 <: ScalarLinearDomain,
                                          D2 <: ScalarLinearDomain}
    F = MOI.ScalarAffineFunction{Float64}

    cid = ref2id(cref)

    r = row(m, cref)
    add_bound(m, r, newdom)

    newcref = MOI.ConstraintIndex{F, D2}(cid)
    return newcref
end

## Delete #####################################################################
###############################################################################

function MOI.is_valid(model::MosekModel,
                      ci::MOI.ConstraintIndex{<:MOI.ScalarAffineFunction{Float64},
                                              S}) where S<:ScalarLinearDomain
    return allocated(model.c_block, ci.value) && getconbound(model.task, row(model, ci))[1] == bound_key(S)
end

if Mosek.getversion() >= (10,0,0)
function MOI.delete(m::MosekModel,
                    cref::MOI.ConstraintIndex{F,D}) where{F <: MOI.VectorAffineFunction{Float64},D <: ACCVectorDomain}
    MOI.throw_if_not_valid(m, cref)

    accid = cref.value
    afeidxs = Mosek.getaccafeidxlist(accid)
    Mosek.putacc(m.task,
                 accid,
                 0,
                 Int64[],
                 Float64[])
    deallocate(m.afes,afeidxs)
end
end # if Mosek.getversion() >= 10

function MOI.delete(
    m::MosekModel,
    cref::MOI.ConstraintIndex{F,D}) where {F <: MOI.ScalarAffineFunction{Float64},
                                           D <: ScalarLinearDomain}
    MOI.throw_if_not_valid(m, cref)

    delete_name(m, cref)

    subi = getindexes(m.c_block, cref.value)

    n = length(subi)
    subi_i32 = convert(Vector{Int32}, subi)
    ptr = fill(Int64(0), n)
    putarowlist(m.task,subi_i32,ptr,ptr,Int32[],Float64[])
    b = fill(0.0,n)
    putconboundlist(m.task,subi_i32,fill(MSK_BK_FX,n),b,b)

    deleteblock(m.c_block, cref.value)
end

function MOI.is_valid(model::MosekModel,
                      ci::MOI.ConstraintIndex{MOI.SingleVariable,
                                              S}) where S<:Union{ScalarLinearDomain,
                                                                 MOI.Integer}
    return allocated(model.x_block, ci.value) && has_flag(model, _variable(ci), S)
end
function MOI.delete(
    m::MosekModel,
    ci::MOI.ConstraintIndex{MOI.SingleVariable, S}) where S<:Union{ScalarLinearDomain,
                                                                   MOI.Integer}
    MOI.throw_if_not_valid(m, ci)
    delete_name(m, ci)
    vi = _variable(ci)
    unset_flag(m, vi, S)
    delete_variable_constraint(m, column(m, vi), S)
end
function MOI.is_valid(model::MosekModel,
                      ci::MOI.ConstraintIndex{MOI.VectorOfVariables,
                                              S}) where S<:VectorCone
    if !(ci.value in eachindex(model.variable_to_vector_constraint_id))
        return false
    end
    id = cone_id(model, ci)
    return 1 ≤ id ≤ getnumcone(model.task) &&
        getconeinfo(model.task, id)[1] == cone_type(S)
end
function MOI.delete(model::MosekModel,
                    ci::MOI.ConstraintIndex{MOI.VectorOfVariables, <:VectorCone})
    id = cone_id(model, ci)

    for vi in MOI.get(model, MOI.ConstraintFunction(), ci).variables
        model.variable_to_vector_constraint_id[vi.value] = 0
    end
    removecones(model.task, [id])
    # The conic constraints with id higher than `id` are renumbered.
    map!(i -> i > id ? i - 1 : i,
         model.variable_to_vector_constraint_id,
         model.variable_to_vector_constraint_id)
end
function MOI.is_valid(model::MosekModel,
                      ci::MOI.ConstraintIndex{MOI.VectorOfVariables,
                                              MOI.PositiveSemidefiniteConeTriangle})
    # TODO add supports for deletion
    return 1 ≤ ci.value ≤ length(model.sd_dim)
end


## List #######################################################################
###############################################################################
function MOI.get(m::MosekModel, ::MOI.ListOfConstraintAttributesSet)
    set = MOI.AbstractConstraintAttribute[]
    if !isempty(m.constrnames)
        push!(set, MOI.ConstraintName())
    end
    # TODO add VariablePrimalStart when get is implemented on it
    return set
end

## Name #######################################################################
###############################################################################
function MOI.supports(::MosekModel, ::MOI.ConstraintName,
                      ::Type{<:MOI.ConstraintIndex})
    return true
end



if Mosek.getversion() >= (10,0,0)

function MOI.set(m::MosekModel, ::MOI.ConstraintName, ci::MOI.ConstraintIndex{F,D},name ::AbstractString) where{F <: MOI.VectorAffineFunction{Float64},D <: ACCVectorDomain}

    putaccname(m.task,ci.value,name)
end
function MOI.get(m::MosekModel, ::MOI.ConstraintName, ci::MOI.ConstraintIndex{F,D}) where{F <: MOI.VectorAffineFunction{Float64},D <: ACCVectorDomain}
    # All rows should have same name so we take the first one
    return getaccname(m.task, ci.value)
end

end # Mosek.getversion() >= 10


function MOI.set(m::MosekModel, ::MOI.ConstraintName, ci::MOI.ConstraintIndex,
                 name ::AbstractString)
    delete_name(m, ci)
    if !haskey(m.constrnames, name)
        m.constrnames[name] = MOI.ConstraintIndex[]
    end
    push!(m.constrnames[name], ci)
    set_row_name(m, ci, name)
end
function MOI.get(m::MosekModel, ::MOI.ConstraintName,
                 ci::MOI.ConstraintIndex{MOI.ScalarAffineFunction{Float64}})
    # All rows should have same name so we take the first one
    return getconname(m.task, getindexes(m.c_block, ref2id(ci))[1])
end


function MOI.get(m::MosekModel, ::MOI.ConstraintName, ci::MOI.ConstraintIndex)
    return get(m.con_to_name, ci, "")
end
function MOI.get(m::MosekModel, CI::Type{<:MOI.ConstraintIndex}, name::String)
    #asgn, row = getconnameindex(m.task, name)
    #if iszero(asgn)
    #    return nothing
    #else
    #    # TODO how to recover function and constraint type ?
    #end
    if !haskey(m.constrnames, name)
        return nothing
    end
    cis = m.constrnames[name]
    if isempty(cis)
        return nothing
    end
    if !isone(length(cis))
        error("Multiple constraints have the name $name.")
    end
    ci = first(cis)
    if !(ci isa CI)
        return nothing
    end
    return ci
end
