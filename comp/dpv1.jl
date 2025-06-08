### A Pluto.jl notebook ###
# v0.20.4

using Markdown
using InteractiveUtils

# ╔═╡ d9b585dc-9063-4754-9c65-8ef7e176e41c
using Test

# ╔═╡ 603bcdaa-c58a-11ef-23c7-99c1edef4481
md"""
# Algorithms
**Dasgupta, Papadimitriou, and Vazirani**

Examples and exercises from the most concise algorithms book in *Julia*.

## Chapter 1: Algorithms with Numbers
"""

# ╔═╡ 475e1a3c-300f-43fd-ae7c-0255ed91f7f3
md"""
### 1.1: Basic Arithmetic

Define a type `BInt` for calculations with arbitrary-size whole numbers.

BUGS: although it should be possible to do calculations with `BInt`s of
arbitrary size, `bvalue` currently returns -1 for anything bigger than an `Int64`,
and it would be necessary to supply a bit vector to create large `Bint`s.
"""

# ╔═╡ af9534f1-4e21-45b7-8aad-157ebd37ab32
begin
	struct BInt <: Integer
		bits::BitVector
	end

	function BInt(n::Int) :: BInt
		@assert n >= 0
		bv = BitVector()
		while n > 0
			n, b = divrem(n, 2)
			push!(bv, b)
		end
		return BInt(bv)
	end

	function bbits(b::BInt) :: Int
		return length(b.bits)
	end
	
	function bvalue(b::BInt) :: Int
		if bbits(b) > 8*sizeof(Int)
			return -1
		end
		v = 0
		for (i, bit) ∈ enumerate(b.bits)
			v += bit * 2^(i-1)
		end
		return v
	end
	
	function Base.show(io::IO, b::BInt)
		bitstring = join(map(x -> x ? "1" : "0", reverse(b.bits)))
		value = bvalue(b)
		if value >= 0
	    	print(io, "BInt($(value): $(bitstring))")
		else
			print(io, "BInt($bitstring))")
		end
	end
end

# ╔═╡ d91ac06b-ace0-4c6d-a8d4-90a5624e9642
begin
	function Base.:(==)(a::BInt, b::BInt) :: Bool
		return a.bits == b.bits
	end
	function Base.:>(a::BInt, b::BInt) :: Bool
		return !(a==b || a<b)
	end
	function Base.:>=(a::BInt, b::BInt) :: Bool
		return !(a<b)
	end
	function Base.:<=(a::BInt, b::BInt) :: Bool
		return a==b || a<b
	end
end

# ╔═╡ 192f9e9c-51ef-4f4a-a4d8-85ded6697376
function Base.:<(a::BInt, b::BInt) :: Bool
	# first, compare the lengths of the bit vectors
	if bbits(a) > bbits(b)
		return false
	elseif bbits(a) < bbits(b)
		return true
	else  # failing that, compare bit-by-bit
		x, y = reverse(a.bits), reverse(b.bits)
		@assert length(x) == length(y)
		for i ∈ length(x):-1:1  # from msb to lsb
			if x[i] < y[i]
				return true
			elseif x[i] > y[i]
				return false
			end
		end
		return false # numbers are equal
	end
end

# ╔═╡ f7677125-4114-463c-9557-22628b9b8b6f
@testset "BInt equality and inequalities" begin
	@test BInt(0) == BInt(0)
	@test BInt(0) ≠ BInt(1)
	@test BInt(1) ≠ BInt(2)
	@test BInt(3) > BInt(0)
	@test BInt(1) < BInt(2)
	@test BInt(2) < BInt(3)
	@test !(BInt(2) < BInt(2))
	@test !(BInt(2) >= BInt(3))
end

# ╔═╡ 4d6b4349-472c-4fb7-b016-6b7f3fc011cc
function trim_leading_zeros(x::BitArray) :: BitArray
	xrev = reverse(x)  # recall bits are lsb-first
	idx = findfirst(x -> x, xrev)  # trim leading zeros
	return isnothing(idx) ? [] : reverse(xrev[idx:end])
end

# ╔═╡ 2214feae-d6eb-4b64-abe3-829979952c7d
function Base.:*(a::BInt, b::BInt) :: BInt
	if b == BInt(0)
		return BInt(0)
	end
	z = a * (b >> 1)
	if iseven(b)
		return z << 1
	else
		return a + z << 1
	end
end

# ╔═╡ 165797f3-773e-4beb-bd7e-58dbaef1a8c3
function Base.:-(a::BInt, b::BInt) :: BInt
	@assert a >= b "BInts must be non-negative"
	x, y = a.bits, b.bits
	n, m = length(x), length(y)
	append!(y, falses(n-m))
	z = falses(n)
	borrow = false
	for i ∈ 1:n
		s = x[i] - y[i] - borrow  # -2..1
		borrow = s < 0 ? true : false
		z[i] = 2*borrow + s
	end
	return BInt(trim_leading_zeros(z))
end

# ╔═╡ bd0e4044-1518-413b-be59-e41b24318e6a
function Base.:+(a::BInt, b::BInt) :: BInt
	if bbits(a) < bbits(b)
		a, b = b, a
	end
	x, y = a.bits, b.bits
	n, m = length(x), length(y)
	append!(y, falses(n-m))
	z = falses(n)
	carry = false
	for i ∈ 1:n
		s = x[i] + y[i] + carry
		z[i] = s == 1 || s == 3
		carry = s == 2 || s == 3
	end
	if carry
		push!(z, true)
	end
    return BInt(z)
end

# ╔═╡ 9ec587e1-b339-4d75-b67d-6451ecaacb63
begin
	function Base.iszero(a::BInt) :: Bool
		return iszero(bbits(a))
	end
	function Base.:<<(a::BInt, n::Int)
		if iszero(a)
			return a
		else
			return BInt(vcat(falses(n), a.bits))
		end
	end
	function Base.:>>(a::BInt, n::Int)
		return BInt(a.bits[n+1:end])
	end
end

# ╔═╡ 7e3731b5-c40b-4bfc-b624-cd6d5b40fbaf
@testset "shift_left and shift_right" begin
	@test iszero(BInt(0) << 1)
	@test BInt(1) << 1 == BInt(2)
	@test BInt(1) << 2 == BInt(4)
	@test BInt(5) << 1 == BInt(10)
	@test iszero(BInt(1) >> 1)
	@test BInt(4) >> 1 == BInt(2)
	@test BInt(5) >> 1 == BInt(2)
	@test BInt(12) >> 2 == BInt(3)
end

# ╔═╡ 49c892e3-8907-43f1-ae9b-88b85f96e887
begin
	function Base.iseven(a::BInt) :: Bool
		return !isodd(a)
	end
	function Base.isodd(a::BInt) :: Bool
		if iszero(a)
			return false
		else
			return a.bits[1]
		end
	end
end

# ╔═╡ 534aa08c-5f35-4901-ad92-3f31200879fd
iseven

# ╔═╡ 31a09cf0-3f1f-4df5-b7bd-32239f57af64
@testset "BInt iseven" begin
	@test iseven(BInt(0)) == true
	@test iseven(BInt(1)) == false
	@test iseven(BInt(6)) == true
	@test iseven(BInt(7)) == false
end

# ╔═╡ e3ee74d5-ecc0-49e6-af59-5da8f76cfeef
@testset "BInt addition and subtraction" begin
	@test BInt(0) + BInt(0) == BInt(0)
	@test BInt(0) + BInt(1) == BInt(1)
	@test BInt(3) + BInt(4) == BInt(7)
	@test BInt(1) - BInt(0) == BInt(1)
	@test BInt(7) - BInt(3) == BInt(4)
	@test BInt(13) - BInt(13) == BInt(0)
	@test_throws AssertionError BInt(5) - BInt(10)
end

# ╔═╡ d2d8df6f-7506-4339-a8ab-59459080559e
@testset "BInt multiplication (a la francais)" begin
	@test BInt(0) * BInt(0) == BInt(0)
	@test BInt(0) * BInt(3) == BInt(0)
	@test BInt(3) * BInt(0) == BInt(0)
	@test BInt(1) * BInt(1) == BInt(1)
	@test BInt(2) * BInt(5) == BInt(10)
	@test BInt(5) * BInt(2) == BInt(10)
end

# ╔═╡ 94759e6e-b62b-4403-922e-1049ac200447
function Base.divrem(a::BInt, b::BInt) :: Tuple{BInt, BInt}
	@assert b > BInt(1)
	if iszero(a)
		return BInt(0), BInt(0)
	else
		q, r = divrem(a >> 1, b)
		q, r = q << 1, r << 1
		r = isodd(a) ? r + BInt(1) : r
		if r >= b
			q, r = q + BInt(1), r - b
		end
		return q, r
	end
end

# ╔═╡ 859234db-00a3-46e4-a18f-9afe2d623c75
@testset "BInt divrem" begin
	@test divrem(BInt(0), BInt(5)) == (BInt(0), BInt(0))
	@test divrem(BInt(15), BInt(3)) == (BInt(5), BInt(0))
	@test divrem(BInt(15), BInt(5)) == (BInt(3), BInt(0))
	@test divrem(BInt(15), BInt(4)) == (BInt(3), BInt(3))
end

# ╔═╡ d56bb28b-c262-4bc7-8a9f-967e87770ba6
md"""
→ *This completes development of the `BInt` type, with facilities for construction, display, comparison, and the four basic operations.*

-------------
"""

# ╔═╡ 71c9d31c-cc93-4e5f-ac67-532bf88c3ac9
md"""
### 1.2: Modular Arithmetic

Although it would be possible to build on the BInt type, we will instead
switch over to conventional Julia types and libraries. This pattern strikes
a balance between practicing low-level work on implementation on the one
hand, and staying close to idiomatic Julia on the other.

To start, we need to develop a set of primitives to handle basic operations
(addition, subtraction, multiplication, division) – as well as exponentiation
and GCD – modulo N. We use Julia's integer types, including `BigInt`, as a base.

A general tactic with these functions is to use the substitution principle to reduce intermediate results modulo N whenever possible.
"""

# ╔═╡ fbb1a97d-af62-40b2-a2ba-56d5ba7d75f5
function addmod(a::Integer, b::Integer, N::Integer) :: Integer
	# `mod` could be implemented along the lines of `divrem` above
	a, b = mod(a, N), mod(b, N)
	c = a + b
	return c < N ? c : c-N  # equivalent to mod(a+b)
end

# ╔═╡ 96aba1d6-a199-4589-859b-b9fda3fc58d1
function multmod(a::Integer, b::Integer, N::Integer) :: Integer
	a, b = mod(a, N), mod(b, N)
	return mod(a*b, N)
end

# ╔═╡ e753c5c1-0a38-4a0e-95cd-946b82e9bfc1
"""
Return ``a^b\\mod N``
"""
function expmod(a::Integer, b::Integer, N::Integer) :: Integer
	a, b = mod(a, N), mod(b, N)
	if iszero(b)
		return 1
	end
	c = expmod(a, div(b, 2), N)
	if iseven(c)
		return mod(c*c, N)
	else
		return mod(a*c*c, N)
	end
end

# ╔═╡ 6648f02d-beac-460e-9029-fe757593e998
"""
Return ``\\gcd (a, b)`` using Euclid's algorithm
"""
function euclid(a::Integer, b::Integer) :: Integer

	function euclid_rec(a, b)
		if iszero(b)
			return a
		else
			return euclid_rec(b, mod(a, b))
		end
	end
		
	@assert a ≥ 0 && b ≥ 0
	if a < b
		a, b = b, a
	end
	return euclid_rec(a, b)
end

# ╔═╡ bcb523bf-4bf2-4bd4-90f6-5a47225c99af
"""
Return integers ``x, y, d``, where ``d = ax + by = \\gcd (a, b)``
"""
function extended_euclid(a::Integer, b::Integer)

	function euclid_rec(a, b)
		if iszero(b)
			return 1, 0, a
		end
		x, y, d = euclid_rec(b, mod(a, b))
		return y, x - div(a, b)*y, d
	end
	
	@assert a ≥ 0 && b ≥ 0
	if a < b
		a, b = b, a
	end
	return euclid_rec(a, b)
end

# ╔═╡ 10e2ecbb-3b49-4fd3-9ae0-be5a91950495
md"""
**Modular division.** $x$ is the _multiplicative inverse_ of $a$ modulo $N$
iff $a x \equiv 1\mod N$. This inverse exists iff $a$ and $N$ are
relatively prime.

Julia uses `invmod` for this, and raises an error if $\gcd (a, N) ≠ 1$.
"""

# ╔═╡ 2572377e-ba38-404f-9046-5363434de08d
function my_invmod(a, N)
	x, y, d = extended_euclid(N, a)
	@assert d == 1 "arguments must be relatively prime"
	return mod(y, N) # y may be negative
end

# ╔═╡ ebefce4d-efe9-4702-8182-06cdff682d14
function divmod(a, b, N)
	binv = my_invmod(b, N)
	return multmod(a, binv, N)
end

# ╔═╡ 79cb59f7-664d-426b-9b38-e854f777eef1
md"""
→ *Useful arithmetic functions built in to Julia:*

- `gcd`
- `gcdx`
- `lcm`
- `powermod`
- `invmod`

-------------
"""

# ╔═╡ 32779dd9-ee80-41ae-9679-23e35c0cc472
md"""
### 1.3: Primality Testing
"""

# ╔═╡ a56ab240-de83-486a-9aa4-db5ace670e2e
"""
Pick a random positive integer from `1...N`
"""
function randpos(n::T) :: T where T <: Integer
	@assert n > 0
	if typeof(n) == BigInt # workaround since rand doesn't support BigInt
		bound = min(n, typemax(UInt64))
		a = mod(rand(UInt64), 1:bound)
		return BigInt(a)
	else
		return mod(rand(typeof(n)), 1:n)
	end
end

# ╔═╡ 273aef63-3e6c-4508-9da3-03627903267d
"""
Use Fermat's little theorem to determine whether a positive integer `n` is likely
to be prime.
"""
function pseudoprime1(n::Integer) :: Bool
	@assert n > 0
	a = randpos(n)
	return powermod(a, n-1, n) == 1
end

# ╔═╡ 52a11e93-68e9-4c46-9f56-4ef65b5875ed
"""
Like pseudoprime1, but testing whether any of `k` random numbers from `1...n`
fails the FLT primality test. May fail for Carmichael numbers, or with probability
``2^{-k}``.

Note: Carmichael numbers fool the FLT test for all `a` from `1...n` that are
_relatively prime_ to `n`. The smallest Carmichael number, 561, has factors 3, 11, and 17. So with a reasonably large choice of `k`, there is still a good chance
of picking an `a` that is _not_ relatively prime, and therefore identifying `n`
as composite.|
"""
function pseudoprime2(n::Integer; k::Int=100) :: Bool
	A = [randpos(n-1) for i ∈ 1:k]
	FLT = [powermod(a, n-1, n) == 1 for a in A]
	return all(FLT)
end

# ╔═╡ acb9bb9a-84a4-4867-a753-7bb5c6b73466
"""
Rewrite `n` as ``2^t u``, returning `(u, t)`
"""
function factor_twos(n::T) :: Tuple{T, Int} where T <: Integer
	@assert n > 0
	u, t = n, 0
	while u > 1 && iszero(u%2)
		u, t = u÷2, t+1
	end
	return u, t
end

# ╔═╡ 32fbe9e5-9dda-48c9-8e03-2b3aa2dd1f72
function rabin_miller(a::T, n::T) :: Bool where T <: Integer
	u, t = factor_twos(n-1)
	S = [powermod(a, 2^i * u, n) for i ∈ 0:t]
	if last(S) ≠ 1  # FLT test
		return false
	end
	i = findfirst(S.==1)
	if i > 1 && S[i-1] ≠ n-1 # -1 mod n
		return false  # nontrivial square root found
	end
	return true
end

# ╔═╡ 0bb594ec-0c2e-4c3a-b148-4620fec4fe9e
function pseudoprime3(n::Integer; k::Int=100) :: Bool
	return all([rabin_miller(randpos(n-1), n) for i ∈ 1:k])
end

# ╔═╡ a3b778c3-e8c5-470f-8dac-96d55742c262
@testset "pseudoprimes" begin
	@test pseudoprime2(97)
	@test !pseudoprime2(97*13)
	@test !pseudoprime3(561)  # designed to catch Carmichael numbers
end

# ╔═╡ 9c7f3dfd-8126-47ea-bdad-ddde386ee75b
function rand_prime(t)
	n = typemax(t)
	@assert n <= typemax(Int128)  # UInt128 edge case
	while true
		r = Int128(rand(0:n-1))
		if pseudoprime3(r)
			return r
		end
	end
end

# ╔═╡ 71237f42-edbd-45ca-a965-586eb05e2230
md"-------------------"

# ╔═╡ c50f003a-13c3-497c-9032-09bd93e9ac5d
md"""
### 1.4: Cryptography

#### RSA public-key system: toy 32-bit version
"""

# ╔═╡ 8787382a-430f-4b99-ad32-3b91cb35ff99
function gen_keys()

	function rel_prime(n)
		for i ∈ 3:n
			if gcd(i, n) == 1
				return i
			end
		end
	end
	
	p, q = rand_prime(Int32), rand_prime(Int32)
	N::Int64 = p*q
	e = rel_prime((p-1)*(q-1))
	public = (N, e)
	private = (invmod(e, (p-1)*(q-1)), e)
	return public, private
end

# ╔═╡ aca45906-e8ea-4faf-befc-a4fb115dc280
function string2ints(s::String) :: Vector{UInt64}
    bytes = codeunits(s)
	pad = 8 - length(bytes) % 8
	if pad > 0
		append!(bytes, UInt8['x' for _ in 1:pad])
	end
	
    num_groups = length(bytes) ÷ 8
    result = Vector{Int64}(undef, num_groups)

    for i in 1:num_groups
        # Calculate the start and end indices of the current group
        start_idx = (i - 1) * 8 + 1
        end_idx = i * 8

        # Pack the current group into an Int64
        group_int = Int64(0)
        for j in 0:7
            group_int |= UInt64(bytes[start_idx + j]) << (8 * (7 - j))
        end
        result[i] = group_int
    end

    return result
end

# ╔═╡ 7e617086-fad0-40ef-93b5-1d525c5807d8
function ints2string(v::Vector{UInt64}) :: String
    uint8_vec = UInt8[]
    for n in v
        bytes = reverse(reinterpret(UInt8, [n]))
        append!(uint8_vec, bytes)
    end
    return String(uint8_vec)
end

# ╔═╡ 976fe9f4-d415-4836-8bd6-05f37b5a09ee
string2ints("hello")

# ╔═╡ 0a84f27e-f02e-4152-be1c-9f5ac32ed62f
function rsa64_encrypt(msg::String, key::Tuple{Integer, Integer}) :: Vector{Int64}
	bytes = string2ints(msg)
	
end

# ╔═╡ bfa2adf8-6a70-45ac-aa90-9398fbbcf248
begin
	p1q1 = 487184289898058016
	mods = [gcd(i, p1q1) for i ∈ 3:20]
	mods .== 1
end

# ╔═╡ 80195a03-072b-4702-b56e-4c2c3416e8c1
md"""
### Setup
"""

# ╔═╡ 00000000-0000-0000-0000-000000000001
PLUTO_PROJECT_TOML_CONTENTS = """
[deps]
Test = "8dfed614-e22c-5e08-85e1-65c5234f0b40"
"""

# ╔═╡ 00000000-0000-0000-0000-000000000002
PLUTO_MANIFEST_TOML_CONTENTS = """
# This file is machine-generated - editing it directly is not advised

julia_version = "1.11.2"
manifest_format = "2.0"
project_hash = "71d91126b5a1fb1020e1098d9d492de2a4438fd2"

[[deps.Base64]]
uuid = "2a0f44e3-6c83-55bd-87e4-b1978d98bd5f"
version = "1.11.0"

[[deps.InteractiveUtils]]
deps = ["Markdown"]
uuid = "b77e0a4c-d291-57a0-90e8-8db25a27a240"
version = "1.11.0"

[[deps.Logging]]
uuid = "56ddb016-857b-54e1-b83d-db4d58db5568"
version = "1.11.0"

[[deps.Markdown]]
deps = ["Base64"]
uuid = "d6f4376e-aef5-505a-96c1-9c027394607a"
version = "1.11.0"

[[deps.Random]]
deps = ["SHA"]
uuid = "9a3f8284-a2c9-5f02-9a11-845980a1fd5c"
version = "1.11.0"

[[deps.SHA]]
uuid = "ea8e919c-243c-51af-8825-aaa63cd721ce"
version = "0.7.0"

[[deps.Serialization]]
uuid = "9e88b42a-f829-5b0c-bbe9-9e923198166b"
version = "1.11.0"

[[deps.Test]]
deps = ["InteractiveUtils", "Logging", "Random", "Serialization"]
uuid = "8dfed614-e22c-5e08-85e1-65c5234f0b40"
version = "1.11.0"
"""

# ╔═╡ Cell order:
# ╟─603bcdaa-c58a-11ef-23c7-99c1edef4481
# ╟─475e1a3c-300f-43fd-ae7c-0255ed91f7f3
# ╠═af9534f1-4e21-45b7-8aad-157ebd37ab32
# ╠═192f9e9c-51ef-4f4a-a4d8-85ded6697376
# ╠═d91ac06b-ace0-4c6d-a8d4-90a5624e9642
# ╟─f7677125-4114-463c-9557-22628b9b8b6f
# ╠═bd0e4044-1518-413b-be59-e41b24318e6a
# ╠═4d6b4349-472c-4fb7-b016-6b7f3fc011cc
# ╠═165797f3-773e-4beb-bd7e-58dbaef1a8c3
# ╟─e3ee74d5-ecc0-49e6-af59-5da8f76cfeef
# ╠═9ec587e1-b339-4d75-b67d-6451ecaacb63
# ╟─7e3731b5-c40b-4bfc-b624-cd6d5b40fbaf
# ╠═534aa08c-5f35-4901-ad92-3f31200879fd
# ╠═49c892e3-8907-43f1-ae9b-88b85f96e887
# ╟─31a09cf0-3f1f-4df5-b7bd-32239f57af64
# ╠═2214feae-d6eb-4b64-abe3-829979952c7d
# ╟─d2d8df6f-7506-4339-a8ab-59459080559e
# ╠═94759e6e-b62b-4403-922e-1049ac200447
# ╟─859234db-00a3-46e4-a18f-9afe2d623c75
# ╟─d56bb28b-c262-4bc7-8a9f-967e87770ba6
# ╟─71c9d31c-cc93-4e5f-ac67-532bf88c3ac9
# ╠═fbb1a97d-af62-40b2-a2ba-56d5ba7d75f5
# ╠═96aba1d6-a199-4589-859b-b9fda3fc58d1
# ╠═e753c5c1-0a38-4a0e-95cd-946b82e9bfc1
# ╠═6648f02d-beac-460e-9029-fe757593e998
# ╠═bcb523bf-4bf2-4bd4-90f6-5a47225c99af
# ╟─10e2ecbb-3b49-4fd3-9ae0-be5a91950495
# ╠═2572377e-ba38-404f-9046-5363434de08d
# ╠═ebefce4d-efe9-4702-8182-06cdff682d14
# ╟─79cb59f7-664d-426b-9b38-e854f777eef1
# ╟─32779dd9-ee80-41ae-9679-23e35c0cc472
# ╠═a56ab240-de83-486a-9aa4-db5ace670e2e
# ╠═273aef63-3e6c-4508-9da3-03627903267d
# ╠═52a11e93-68e9-4c46-9f56-4ef65b5875ed
# ╠═acb9bb9a-84a4-4867-a753-7bb5c6b73466
# ╠═32fbe9e5-9dda-48c9-8e03-2b3aa2dd1f72
# ╠═0bb594ec-0c2e-4c3a-b148-4620fec4fe9e
# ╠═a3b778c3-e8c5-470f-8dac-96d55742c262
# ╠═9c7f3dfd-8126-47ea-bdad-ddde386ee75b
# ╟─71237f42-edbd-45ca-a965-586eb05e2230
# ╟─c50f003a-13c3-497c-9032-09bd93e9ac5d
# ╠═8787382a-430f-4b99-ad32-3b91cb35ff99
# ╠═aca45906-e8ea-4faf-befc-a4fb115dc280
# ╠═7e617086-fad0-40ef-93b5-1d525c5807d8
# ╠═976fe9f4-d415-4836-8bd6-05f37b5a09ee
# ╠═0a84f27e-f02e-4152-be1c-9f5ac32ed62f
# ╠═bfa2adf8-6a70-45ac-aa90-9398fbbcf248
# ╟─80195a03-072b-4702-b56e-4c2c3416e8c1
# ╠═d9b585dc-9063-4754-9c65-8ef7e176e41c
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
