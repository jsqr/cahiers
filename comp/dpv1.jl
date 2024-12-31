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
		x, y = reverse(a.bits), reverse(b.bits) # msb first
		@assert length(x) == length(y)
		for i ∈ 1:length(x)
			if x[i] > y[i]
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
	@test !(BInt(2) < BInt(2))
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
	zrev = reverse(z)  # recall bits are lsb-first
	idx = findfirst(x -> x, zrev)  # trim leading zeros
	if isnothing(idx)
		return BInt(0)
	else
		return BInt(reverse(zrev[idx:end]))
	end
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

# ╔═╡ e3ee74d5-ecc0-49e6-af59-5da8f76cfeef
@testset "BInt addition and subtraction" begin
	@test BInt(0) + BInt(0) == BInt(0)
	@test BInt(0) + BInt(1) == BInt(1)
	@test BInt(3) + BInt(4) == BInt(7)
	@test BInt(1) - BInt(0) == BInt(1)
	@test BInt(7) - BInt(3) == BInt(4)
	@test BInt(13) - BInt(13) == BInt(0)
end

# ╔═╡ 80195a03-072b-4702-b56e-4c2c3416e8c1
md"""
### Setup
"""

# ╔═╡ c6f8317e-181c-44ff-b2f3-6136c7e9b347


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
# ╠═165797f3-773e-4beb-bd7e-58dbaef1a8c3
# ╟─e3ee74d5-ecc0-49e6-af59-5da8f76cfeef
# ╟─80195a03-072b-4702-b56e-4c2c3416e8c1
# ╠═d9b585dc-9063-4754-9c65-8ef7e176e41c
# ╠═c6f8317e-181c-44ff-b2f3-6136c7e9b347
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
