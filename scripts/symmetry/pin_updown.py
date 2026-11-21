"""Rule 'up adjacent, down to the bottom' for tree shapes: insert alternatives in breadth-first
order from a root; an alternative above its parent goes directly above the parent, one below
its parent goes to the bottom of the current ranking."""
import itertools, sys
from pin_tree_uniform import check
def updown_rule(alts, S, root):
    adj = {x: [] for x in alts}
    for u, v in S: adj[u].append(v); adj[v].append(u)
    order, parent = [root], {root: None}
    for x in order:
        for y in sorted(adj[x]):
            if y not in parent: parent[y] = x; order.append(y)
    out = {}
    for pat in itertools.product((0, 1), repeat=len(S)):
        bit = dict(zip(S, pat)); rank = [root]
        for y in order[1:]:
            x = parent[y]; up = bit[(x, y)] == 0 if (x, y) in bit else bit[(y, x)] == 1
            if up: rank.insert(rank.index(x), y)
            else: rank.append(y)
        out[pat] = "".join(rank)
    return out
if __name__ == "__main__":
    for m in map(int, sys.argv[1:]): check(m, updown_rule)
