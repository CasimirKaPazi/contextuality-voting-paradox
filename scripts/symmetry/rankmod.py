import itertools
P = 1_000_003
def rank_mod(rows):
    M = [[x % P for x in row] for row in rows]; rk = 0
    for col in range(len(M[0])):
        p = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        inv = pow(M[rk][col], P - 2, P); M[rk] = [x * inv % P for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]; M[i] = [(x - f * y) % P for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
