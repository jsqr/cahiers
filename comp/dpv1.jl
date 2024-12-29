### A Pluto.jl notebook ###
# v0.20.4

using Markdown
using InteractiveUtils

# ╔═╡ d9b585dc-9063-4754-9c65-8ef7e176e41c
using Primes

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
	    	print(io, "BInt($(bvalue(b)): $(bitstring))")
		else
			print(io, "BInt($bitstring))")
		end
	end
end

# ╔═╡ bd0e4044-1518-413b-be59-e41b24318e6a
function Base.:+(a::BInt, b::BInt)::BInt
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

# ╔═╡ 6e81305b-29e9-4ade-815b-dbcf62120308
x, y = BInt(3), BInt(4)

# ╔═╡ ab123c7d-9870-4096-adea-7cf8b900281f
y+y+x

# ╔═╡ 80195a03-072b-4702-b56e-4c2c3416e8c1
md"""
### Setup
"""

# ╔═╡ 00000000-0000-0000-0000-000000000001
PLUTO_PROJECT_TOML_CONTENTS = """
[deps]
Primes = "27ebfcd6-29c5-5fa9-bf4b-fb8fc14df3ae"

[compat]
Primes = "~0.5.6"
"""

# ╔═╡ 00000000-0000-0000-0000-000000000002
PLUTO_MANIFEST_TOML_CONTENTS = """
# This file is machine-generated - editing it directly is not advised

julia_version = "1.11.2"
manifest_format = "2.0"
project_hash = "d73f56de11521595df61ac8b8108963f579c83b2"

[[deps.IntegerMathUtils]]
git-tree-sha1 = "b8ffb903da9f7b8cf695a8bead8e01814aa24b30"
uuid = "18e54dd8-cb9d-406c-a71d-865a43cbb235"
version = "0.1.2"

[[deps.Primes]]
deps = ["IntegerMathUtils"]
git-tree-sha1 = "cb420f77dc474d23ee47ca8d14c90810cafe69e7"
uuid = "27ebfcd6-29c5-5fa9-bf4b-fb8fc14df3ae"
version = "0.5.6"
"""

# ╔═╡ Cell order:
# ╟─603bcdaa-c58a-11ef-23c7-99c1edef4481
# ╟─475e1a3c-300f-43fd-ae7c-0255ed91f7f3
# ╠═af9534f1-4e21-45b7-8aad-157ebd37ab32
# ╠═bd0e4044-1518-413b-be59-e41b24318e6a
# ╠═6e81305b-29e9-4ade-815b-dbcf62120308
# ╠═ab123c7d-9870-4096-adea-7cf8b900281f
# ╟─80195a03-072b-4702-b56e-4c2c3416e8c1
# ╠═d9b585dc-9063-4754-9c65-8ef7e176e41c
# ╟─00000000-0000-0000-0000-000000000001
# ╟─00000000-0000-0000-0000-000000000002
