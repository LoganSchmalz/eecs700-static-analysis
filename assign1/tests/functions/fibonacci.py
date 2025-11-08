def fib(n):
    requires(n >= 0)
    ensures(ret >= old(n))
    # if n == 0 or n == 1:
    if n <= 1:
        return 1
    else:
        x = fib(n-1) # n-1
        y = fib(n-2) # n-2
        return x + y # 2n-3