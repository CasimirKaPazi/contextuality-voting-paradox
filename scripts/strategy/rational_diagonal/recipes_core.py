def works_PQ(R, P, Q):
    nb, nc = len(R), len(R[0])
    rp = {x: j for j, x in enumerate(P)}; rq = {x: j for j, x in enumerate(Q)}
    colbest = [min(rp[R[b][c]] for b in range(nb)) for c in range(nc)]
    for b in range(nb):
        top = min(rq[R[b][c]] for c in range(nc))
        if not any(rq[R[b][c]] == top and rp[R[b][c]] > colbest[c] for c in range(nc)):
            return False
    return True
