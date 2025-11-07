
def incr(v):
    # precondition: input is non-negative
    requires(v >= 0)
    # postcondition: final v equals initial v + 1
    ensures(ret == old(v) + 1 == v)
    modifies(v)
    # v = v
    # x = v + 1
    # v = x
    v = v + 1
    return v

x = 0
y = 0
while x < 10:
    invariant(x <= 10)
    # invariant(x <= 5)
    # invariant(0 <= x)
    invariant(2*x == y)
    invariant(y >= 0)
    invariant(y <= 20)
    y = incr(y)
    y = incr(y)
    # x = incr(x)
    x = x + 1
assert y == 20
assert x == 10
# assert y == x