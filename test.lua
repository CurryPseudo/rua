local a = 0
local b = 1
if a ~= b then
	a = 1 + a
end
if a == b then
	a = 1 ~= a
end
print(b, a)
