# create an array variable from an unknown source (simulate)
# We'll assign an arrvar symbolically by e.g., A = B where B had no literal created earlier.
# For now, to test, do:
A = [0]    # change or omit to make it unknown; here it's known
i = 0
assert 0 <= i < len(A)