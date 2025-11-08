def silly(x,y):
    modifies(x)
    x = x + 1
    return 0

a = 1
b = 2
silly(a,b)
assert(b == 2)
# should always fail if this line is uncommented
# assert(a == 2)