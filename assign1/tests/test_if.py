n = 5
y = 4
if n == 0:
    n = 0
    y = 4
else:
    n = n - 1
    n = 1
    n = 0
    y = y + 1
assert(n == 0)
assert(y == 4 or y == 5)