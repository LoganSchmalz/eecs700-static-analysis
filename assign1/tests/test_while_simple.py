x = 0
while x < 10:
    invariant(x <= 10)
    x = x + 1
x = 4
while x < 5:
    invariant( x<= 5)
    x = x + 1
y = 0
while y < x:
    invariant(y <= x)
    y = y + 1
assert x == 5
assert y == x