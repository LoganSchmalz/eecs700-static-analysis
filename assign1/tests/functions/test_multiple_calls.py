def incr(v):
    # precondition: input is non-negative
    requires(v >= 0)
    # postcondition: final v equals initial v + 1
    ensures(ret == old(v) + 1 == v)
    modifies(v)
    v = v
    x = v + 1
    v = x
    return v

x = 3
y = 2
y = incr(y)
assert(y == 3)
# assert(__ret_incr_2 == 3)
# assert(x == 3)
x = incr(y)
# assert(__ret_incr_1 == 2)
assert(y == 4)
assert(x == 4)
incr(8)
incr(9)
# assert(x == 5)
# assert(ret == 10)