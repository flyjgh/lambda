import Base: *, ^, +, /, ÷, ⊻, !, ==, show, convert, Int, Bool
# ----------------------------------------------------------------
# Kernel
# φ(α,β) = eval(α)(eval(β))
# φ(α)   = foldl(φ, α)

# macro φ(α...) φ(α) end

# ----------------------------------------------------------------
# Eval
# evalo = α -> quote($a).head == :(=) ? eval(α)

φ(α,β)       = eval(α)(eval(β))
φ(α,β::Expr) = φ(α, φ(atom.(β.args)))
φ(α)         = foldl(φ, atom.(α))

macro φ(α...) φ(α) end


atom(x) = x
atom(x::Int) = ℕ(x)
atom(x::Bool) = Boolean(x)
atom(x::Function) = :($x)

tail(x::Vector{T}) where T = x[2:end]

function atom(expr::Expr)
    expr.head === :tuple && return φ(atom.(expr.args))
    expr.head === :call  && return Expr(:call, atom(first(expr.args)), (atom.(tail(expr.args))...))
    expr.head === :block && return Expr(:block, atom.(expr.args)...)
    expr.head === :->    && return Expr(:->, first(expr.args), atom.(tail(expr.args))...)
    expr.head === :if    && return Expr(ifelse(atom(expr.args[1])(atom(expr.args[2]))(atom(expr.args[3]))))
    expr.head === :(&&)  && return Expr(iff(atom(expr.args[1]))(atom(expr.args[2])))
    expr.head === :(||)  && return Expr(orr(atom(expr.args[1]))(atom(expr.args[2])))
    expr.head === :(=)   && return Expr(:(=), first(expr.args), var(atom(expr.args[2])))
    return expr
end

# ----------------------------------------------------------------
# Combinators
const S = α -> β -> γ -> (α)(γ)((β)(γ))    # (α -> (β -> γ)) -> ((α -> β) -> (α -> γ))
const K = α -> β -> α
const I = α -> α                           # (S)(K)(K)

const ω = (S)(I)(I)                        # γ -> I(γ)(I(γ)) === γ -> γ(γ)

# Ω = (ω)(ω)                               # (γ -> γ(γ))(γ -> γ(γ))
                                           # : self-replicating code

const Y = ƒ->(α->(ƒ)(α)(α))(α->(ƒ)(α)(α))  # : loop

# ----------------------------------------------------------------
# Nat struct
struct ℕ{T} λ end

(ƒ::ℕ)(α) = ƒ.λ(α)

ℕ(ƒ) = ℕ{Int(ƒ)}(ƒ)
ℕ(n::Int,ƒ=zero) = n < 1 ? ℕ{Int(ƒ)}(ƒ) : ℕ(n-1, (succ)(ƒ))

Base.show(io::IO, ::ℕ{T}) where T = println(io, "$T :: ℕ")

# ----------------------------------------------------------------
# Nat
const zero = (K)(I) |> ℕ
const succ = n -> γ -> γ ∘ n(γ)

∑(α) = β -> (α)(succ)(β) |> ℕ
∏(α) = β -> (α ∘ β) |> ℕ
^(α) = β -> (β)(α) |> ℕ

# ----------------------------------------------------------------
# Bool struct
struct Boolean{T} λ end

(ƒ::Boolean)(α) = ƒ.λ(α)

Boolean(ƒ) = Boolean{Bool(ƒ)}(ƒ)
Boolean(b::Bool) = b ? tt : ff

Base.show(io::IO, ::Boolean{T}) where T = println(io, "$T :: Boolean")

# ----------------------------------------------------------------
# Bool
const tt = (K) |> Boolean
const ff = (K)(I) |> Boolean

!(α)  = (α)(ff)(tt) |> Boolean
eq(α) = β -> (α)(β)((!)(β)) |> Boolean
==(α) = β -> (α)(β)((!)(β)) |> Boolean
∧(α)  = β -> (α)(β)(α) |> Boolean
∨(α)  = β -> (α)(α)(β) |> Boolean
⊻(α)  = β -> (α)((!)(β))(β) |> Boolean

# ----------------------------------------------------------------
# Control Flow
iff(::Boolean{T}) where T = β -> T && β
iff(α) = β -> Bool(α) && β
orr(::Boolean{T}) where T = β -> T || β
orr(α) = β -> Bool(α) || β
const ifelse = α -> β -> γ -> (α)(β)(γ)

# ----------------------------------------------------------------
# Var
var(α) = β -> (β)(α)

# ----------------------------------------------------------------
# Pair struct
struct ×{T,N} λ end

(ƒ::×)(α) = ƒ.λ(α)

×(α) = β -> γ -> ×{typeof(α),typeof(β)}((γ)(α)(β))

Base.show(io::IO, ::×{T,N}) where {T,N} = println(io, "$T × $N :: ×")

# ----------------------------------------------------------------
# Pair
# ×(α) = β -> γ -> (γ)(α)(β)

const nil = (K)
const fst = (K)
const snd = (K)(I)

# ----------------------------------------------------------------
# Arity
==(α,β) = (==)(β)(α)
^(α,β) = ^(β)(α)
∧(α,β) = ∧(α)(β)
∨(α,β) = ∨(α)(β)
⊻(α,β) = ⊻(α)(β) 
×(α,β) = ×(α)(β) 

# ----------------------------------------------------------------
# Converters
Int(::ℕ{T}) where T = T
Int(n::T) where T = (n)(α -> α+1)(0)

Bool(::Boolean{T}) where T = T
Bool(b::T) where T = (b)(true)(false)
Bool(e::Expr) = φ(e)

ℕ(::Boolean{T}) where T = !T ? zero : error("::Boolean{T} cannot be converted to ::ℕ if T != false")
Boolean(::ℕ{T}) where T = T == 0 ? ff : error("::ℕ{T} cannot be converted to ::Boolean if T != 0")

# ----------------------------------------------------------------
# (*)(n,ƒ) = ƒ(n)
# (^)(ƒ,n) = ∘(repeat([ƒ], n)...)

# (+)(α::T) where T <: Number = β -> α + +(β)
# (-)(α::T) where T <: Number = β -> α - -(β)
# (*)(α::T) where T <: Number = β -> α - -(β)
# (/)(α::T) where T <: Number = β -> α / /(β)
# (^)(α::T) where T <: Number = β -> α ^ ^(β)
# (÷)(α::T) where T <: Number = β -> α ÷ ÷(β)

# (+)(α,β) = (+)(α)(β)
# (-)(α,β) = (-)(α)(β)
# (*)(α,β) = (*)(α)(β)
# (/)(α,β) = (/)(α)(β)
# (^)(α,β) = (^)(α)(β)
# (÷)(α,β) = (÷)(α)(β)

# ----------------------------------------------------------------

f = x -> y -> ∑(x)(y)
g = w -> x -> y -> z -> ∑(x)(y) |> ∑(z) |> ∑(w)
x, y, z = 3, 4, 5

debug = x -> println(♯(x))
@φ debug (∑, 10, 15)

@φ ∑ (∏, 5, (∑, (∑, 2, 0), 3)) 0
@φ ∑ 10 15
@φ g 2 3 4 2
@φ ∑ (∑(2) ∘ ∑(2), 2) (∑(2) ∘ ∑(2), 2)
@φ ((∑, 2) ∘ (∑, 2)) 10
# @φ g 2 3 y 2

# @φ (x -> x) (∏, 10, 2)
# (@φ (x,y) -> ∑(2))(ℕ(2))
# @φ exp (x -> 2int(x), (∏, 10, 2))

@φ log (exp, Int(10))

@φ x = 5

@φ true ∧ !false ∨ !true ∨ false
@φ true == true
@φ (==, true, false)
@φ true ? true : false
# @φ (2, ==, 2) && (false || true)

@φ (x -> y -> vcat(x,y)) [1:5...] [5:10...]
@φ (x -> x) [1:5...]

@φ true × false fst
@φ true × false × true fst snd



