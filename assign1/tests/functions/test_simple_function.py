def incr(x):
    requires(x >= 0)
    ensures(ret == old(x) + 1)
    x = x + 1
    return x