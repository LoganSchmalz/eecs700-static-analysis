def incr(x):
    ensures(ret == old(x) + 1)
    return x + 1

z = 3
y = incr(z)
assert(y == z + 1)