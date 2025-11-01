# Example functions to exercise function-contract parsing and verification

def incr(v):
    # precondition: input is non-negative
    requires(v >= 0)
    # postcondition: final v equals initial v + 1
    ensures(ret == v == old(v) + 1)
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


# top-level no-op so module isn't empty
pass
