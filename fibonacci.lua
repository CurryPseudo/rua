local i = 0
local a = 0
local b = 1
while i < 30 do
	local c = a + b
	a = b
	b = c
	i = i + 1
end
print(i, a, b)
print()
