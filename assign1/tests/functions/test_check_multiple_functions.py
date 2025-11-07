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

def test(v):
    requires(v == 4)
    ensures(ret == 11)
    return v + 7

def bad_incr(v):
    # same contract but body is incorrect
    requires(v >= 0)
    ensures(v == old(v) + 1)
    v = v + 2
    return v