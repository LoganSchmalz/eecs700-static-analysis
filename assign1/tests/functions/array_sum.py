def sum_array(A, i, s):
    requires(i <= len(A))
    ensures(A == old(A))
    if i >= len(A):
        return s
    else:
        x = s + A[i]
        y = sum_array(A, i+1, x)
        return y
    # b = A[i]
    # return b

A = [0,1,2]
sum_array(A, 0, 0)