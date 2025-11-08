def sub_to_zero(n):
    requires(n >= 0)
    ensures(n == 0)
    modifies(n)
    if n == 0:
        n = 0
        return n
    else:
        n = n - 1
        x = sub_to_zero(n)
        return x