local no = 100000
local not_primes = {}
local i = 2
while i < no do
	if not not_primes[i] then
		print(i)
		if i < math.sqrt(no) then
			local j = 2
			while i * j < no do
				not_primes[i * j] = true
				j = j + 1
			end
		end
	end
	i = i + 1
end

