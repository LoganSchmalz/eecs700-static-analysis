B = [1, 2]
B[1] = 3
A = B
A[0] = 9
assert A[0] == 9
assert A[1] == 3