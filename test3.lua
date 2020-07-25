local a = {3, 4}
local d = function ()
end
local c = {3, 4}
local b = {}
b[a] = 3
b[d] = 5
print(b[c])
print(b[d])
