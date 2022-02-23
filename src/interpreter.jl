# -----------------------------------------------------------

tail(x::Vector{T}) where T = x[2:end]
env_ = y -> error("-$y- not defined")

φ(x::T) where T = x
φ(x::Symbol, env) = env(x)
# function φ(expr::Expr, env=env_)
    # expr.head === :call && return Expr(:call, first(expr.args), φ.(tail(expr.args))...)
    # expr.head === :-> && return α -> φ.(expr.args, ρ -> first(expr.args) == ρ ? α : env(ρ))
    # expr.head === :block && return Expr(:block, φ.(expr.args)...)
# end

φ(x::T) where T = x
function φ(expr::Expr)
    expr.head === :call && return eval(first(expr.args))(φ.(tail(expr.args))...)
    expr.head === :-> && return (α -> φ.(tail(expr.args)))(first(expr.args))
    expr.head === :block && return Expr(:block, φ.(expr.args)...)
end

as = :(begin exp(2) end)
Expr(:block, φ.(as.args)...)

f(x,y) = x + y
g(x,y) = x - y

:(f(g(5,3),5)) |> φ
:(f(2,3) |> ==(5)) |> φ
:(f(2,3) |> x -> 2x) |> φ

expr.head === :-> && return 
as = :((x,y) -> x + y)
dump(as)


(s::String)() = fold(s)
(s::String)(α) = fold(s)(α)
(s::String)(α...) = foldl(fold(s), α)
"f (f x (g 2 y z))"()
"g x"(2,3)

atom(α) = α isa String ? occursin(r"^[+-]?([0-9]+([.][0-9]*)?|[.][0-9]+)$", α) ? parse(Float64, α) : Symbol(α) : α
fold(α,β)     = eval(α)(eval(β))
fold(α)       = foldl(fold, α)

function fold(α::Union{Char,String})
    occursin('(', α) && fold(split(α, "(")[1]), fold(split(α, "(", limit=2)[2])
    occursin(')', α) && return fold(atom.(split(α[1:findfirst(')', α)-1])))
    α isa Char && return fold(atom(α))
    fold(atom.(split(α)))
end

# evalo = α -> foldl(cfold, Symbol.(split(α)))
# evalo = α -> foldl((x,y) -> eval(Expr(:call, cfold(x), cfold(y))), split(α))
f = x -> y -> x + y
g = x -> y -> z -> x - y - z
x, y, z = 3, 4, 5

dump(p)
u.head
e = :((log∘exp)(5 + 3))
s = :((x,w) -> y -> 2x)
h = :((x -> 2x)(2))
u = :(function f(x) x end)
v = :(d = (x,y) -> x*y)
p = :(@⇀ f(x,y,z) = x + y + z)

# ----------------------------------------------------------------

(s::String)() = fold(s)
(s::String)(α) = fold(s)(α)
(s::String)(α...) = foldl(fold(s), α)
"f (f x (g 2 y z))"()
"g 4"(2)(3)  # (2,3,4)

atom(α::T) where T = occursin(r"^[+-]?([0-9]+([.][0-9]*)?|[.][0-9]+)$", α) ? parse(Float64, α) : Symbol(α)

fold(α,β) = eval(α)(eval(β))
fold(α)   = foldl(fold, α)

function fold(α::String)
    occursin('(', α) && return fold(α[findfirst('(', α)+1:end])
    occursin(')', α) && return fold(atom.(split(α[1:findfirst(')', α)-1])))
    fold(atom.(split(α)))
end

# ----------------------------------------------------------------

φ(α,β) = eval(α)(eval(β))
φ(α)   = foldl(φ, α)

macro φ(α...) φ(α) end

# macro φ(α...)
    # < ∈ α && return fold(α[findfirst('(', α)+1:end])
    # > ∈ α && return fold(atom.(split(α[1:findfirst(')', α)-1])))
# end

(@φ f 3)(4)
@φ g 3 4 5
@φ g 3 f 5

f = x -> y -> x + y
g = x -> y -> z -> x - y - z
x, y, z = 3, 4, 5


