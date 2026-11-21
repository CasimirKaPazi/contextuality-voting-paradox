# Loops of Relations

*Working note. It gives one elementary frame for three obstructions that the drafts treat separately: the Liar cycle and the Condorcet cycle (*Cycles and Twists*) and the strategic diagonal (*Walls and Strategy*, Lemma 2). The propositions are proved here and are elementary; the readings are marked. Background: *The Switch Between Fixed Point and No Fixed Point*.*

## 1. A loop of contexts

Take variables x₀, …, x_{n−1}, with x_i taking values in a set V_i, indices read mod n. The contexts are the consecutive pairs C_i = {x_i, x_{i+1}}, and context C_i allows a relation R_i ⊆ V_i × V_{i+1}. A *global section* is a choice of all x_i with (x_i, x_{i+1}) ∈ R_i for every i. A possibilistic model is *compatible* if two contexts allow the same values to each variable they share (Abramsky and Brandenburger; for n = 2 the two contexts share both variables, and the condition is imposed on each separately).

Composing the relations once around the loop gives the *monodromy*

  M = R₀ ; R₁ ; … ; R_{n−1} ⊆ V₀ × V₀,

where x M y means that some x₁, …, x_{n−1} lead from x₀ = x around the loop and back to y.

**Proposition 1.**
(a) Global sections correspond to the points x with x M x.
(b) A compatible model exists exactly when there are non-empty sets A_i ⊆ V_i such that each R_i, restricted to A_i × A_{i+1}, leaves no element of A_i without a partner in A_{i+1} and no element of A_{i+1} without a partner in A_i.
(c) If the sets V_i are finite and a compatible model exists, then some power M^k has a fixed point.

*Proof.* (a) A section, read from x₀ around the loop, is a witness for x₀ M x₀, and conversely. (b) Given such sets, let context C_i allow R_i restricted to A_i × A_{i+1}; both contexts containing x_i then allow it exactly A_i. Conversely, the values a compatible model allows each variable form such sets. (c) By (b), every point of A₀ has an M-successor in A₀. Following successors in the finite set A₀ must repeat a point, x M x′ M … M x, which is a fixed point of M^k for the number k of steps taken. ∎

A fixed point of M^k is a global section of the loop run k times, the *k-fold cover* of the scenario. In the terms of *Four Levels*, read possibilistically:
- the loop is at level 1 if no family as in (b) exists;
- at level 2 if one exists but M has no fixed point;
- consistent if M has a fixed point.

Part (c) says that on finite value sets every possibilistically contextual loop opens up on a finite cover. An obstruction that survives every finite cover needs an infinite value set. This is the precise form of remark (a) of *Cycles and Twists*, Section 3: finite methods do not see the Condorcet obstruction. For a cycle on a finite chain, (c) also gives Proposition 1 of that paper. A model would yield x₀ > x₁ > … > x₀ after k rounds, so no model exists.

## 2. Edges given by a group

Let a group G act on a set V, and let each context allow the moves in a non-empty set Γ_i ⊆ G:

  R_i = {(v, g·v) : g ∈ Γ_i}.

Then x M x exactly when some element of the *holonomy set* H = Γ_{n−1} ⋯ Γ₀ fixes x. Every such model is compatible, since every value has a partner in both directions.

**Proposition 2.** If G acts freely, the loop has a global section exactly when the identity e lies in H. If H is a single element h, there are three cases:
- h = e: a section exists;
- h ≠ e has finite order k: there is no section, but there is one on the k-fold cover;
- h has infinite order: there is no section on any finite cover.

*Proof.* With a free action, h·x = x only for h = e. The k-fold cover has holonomy set H^k, so the second and third cases follow. ∎

The cases of the drafts:

| Loop | G acting on V | Moves Γ_i | Holonomy | Case |
|---|---|---|---|---|
| Liar cycle with an odd number of negations | ℤ/2 on {true, false} | {0} for "equals", {1} for "is the negation of" | {1} | finite order 2: section on the double cover |
| Condorcet n-cycle, unit steps | ℤ on ℤ | {−1} | {−n} | infinite order |
| Condorcet n-cycle on the unbounded line | ℝ on ℝ | (−∞, 0) | (−∞, 0) | e ∉ H: no section on any cover |
| Condorcet n-cycle on the circle, n ≥ 3 | ℝ/ℤ on itself | steps back by less than half a turn | all of the circle | e ∈ H: section (Proposition 2 of *Cycles and Twists*) |
| n-cycle on n equally spaced points | ℤ/m on itself, m = n | {−1} | {0} | section |

On the line the reason is the order. The negative half-line is closed under addition, so a product of moves that each go down goes down and never returns to e. Every ordered group behaves this way. The circle group admits no compatible order, so going down repeatedly wraps around and reaches e.

**Reduction.** A homomorphism φ: G → G′ with an equivariant map V → V′ sends sections to sections and holonomy sets to holonomy sets. So an obstruction downstairs implies one upstairs, and an obstruction upstairs can disappear downstairs.
- **Reduction mod 2.** ℤ → ℤ/2 sends the unit step to negation. A Condorcet n-cycle with unit steps becomes a Liar cycle with n negations, and its obstruction survives exactly when n is odd. Every 3-cycle survives.
- **Reduction mod m.** ℤ → ℤ/m closes the cycle exactly when m divides n.
- **The covering of the circle by the line,** read upwards, is Proposition 4 of *Cycles and Twists*. A placement on the circle lifts exactly when its winding is zero.

This is the map between the two loops asked for in open problem 2 of *Cycles and Twists*. Both are loops with holonomy in a group; reduction mod 2 is a homomorphism of groups; and the Liar's holonomy has finite order while the Condorcet holonomy has infinite order. *(The table and the reduction are proved here; that this answers the open problem is a judgement.)*

## 3. An edge chosen by an adversary

The diagonal of *Walls and Strategy* is a loop of length two. One node is the strategist's strategy b ∈ B; the other is the profile c ∈ C of the other players' strategies. One edge is the strategist's requirement BR = {(c, b) : b is a best reply to c under P}. The other edge is chosen by the opponents: they play a function f from B to C, and may use only functions whose graph lies in an allowed relation A ⊆ B × C. The monodromy of the loop for a given f sends b to the best replies to f(b), and its fixed points are the strategies b that are best replies to f(b).

Two kinds of fixed point must be distinguished:
- b is an **existential** fixed point if b ∈ BR(c) for some c ∈ A(b): the loop closes for some choice of the opponents;
- b is a **universal** fixed point if b ∈ BR(c) for every c ∈ A(b): it closes whatever the opponents choose.

**Proposition 3.** Let every A(b) be non-empty. The opponents have a function f inside A whose monodromy has no fixed point exactly when there is no universal fixed point.

*Proof.* If b is not universal, choose f(b) ∈ A(b) with b ∉ BR(f(b)). Doing this for every b gives a function with no fixed point. If b is universal, b is a fixed point of every f. ∎

The cases:
- **A = B × C, the opponents unrestricted.** The universal fixed points are the dominant strategies, and Proposition 3 is Lemma 2. The programs D_k of the lemma are how the opponents implement f; that every f can be implemented is the single assumption of `lean/Diagonal.lean`. In Lawvere's terms this is the point-surjectivity hypothesis.
- **Two players, A = the opponent's best replies under Q.** The existential fixed points are the strategies that belong to a Nash equilibrium. Universal fixed points are Canning's strict Nash strategies, and Proposition 3 is the rational diagonal.

For loops whose edges are functions, existential and universal fixed points coincide, and Proposition 3 adds nothing to Proposition 1. The Liar and the Condorcet cycle are of this kind, or are relations without any adversary: there the question is only whether some section exists. Strategy needs an edge that is a relation chosen against the player. On tight game forms existential fixed points always exist, since every pair of preferences has an equilibrium, and the open problem of *Walls and Strategy* is whether universal ones can still be missing.

*Reading.* Aggregation paradoxes fail at the existential level: no consistent global answer exists. The strategic barrier fails at the universal level, where answers may exist but none survives every admissible choice of the others. An adversarial edge is a context that picks its admissible value after seeing the rest of the loop. *(Interpretation.)*

## 4. Relation to the three mechanisms of the switch

*The Switch Between Fixed Point and No Fixed Point* names three mechanisms. In the present frame:
1. **No loop.** On a tree of contexts, partial sections extend one edge at a time, so a compatible model always has a section. This is the loop-free case of Vorob'ev's theorem.
2. **Going around twice.** A holonomy of finite order k closes on the k-fold cover (Proposition 2). The Liar is the case k = 2. Proposition 1(c) says that on finite value sets this is the only kind of contextual loop. Canning's alternating hierarchy has the same two-step shape, but it does not fit Proposition 2 directly, since R is a map on sets of programs, not a group action. *(Analogy.)*
3. **Adding a value.** Proposition 2 assumes a free action. A value fixed by the holonomy restores a section: the truth-value gap is fixed by negation, the centre of the disc by rotation, the uniform lottery by renaming the alternatives.

## 5. Open questions

1. *Set-valued holonomy.* Ghrist and Cooperband treat visual paradoxes as torsors with a holonomy element. The Condorcet cycle on the line has a holonomy *set*, a cone in an ordered group. Is there a cohomology with coefficients in pairs (G, cone) whose class vanishes exactly when e ∈ H?
2. *Beyond single loops.* The contexts of Arrow's scenario are triples, and their nerve is not a single loop. Atserias and Kolaitis reduce cyclic hypergraphs to modular counting around cycles. Do the levels of *Four Levels* reduce to the loops of Proposition 1 in the same way?
3. *Universal fixed points on tight forms.* This is open problem 1 of *Walls and Strategy*, now stated as a fixed-point question. In which tight forms does every pair of strict preferences give some player a strategy that is a fixed point for every admissible reply of the opponent?
4. *Formal check.* Propositions 1 to 3 are elementary and suitable for the Lean development, where Proposition 3 with A = B × C would restate `Diagonal.lean`.

## References

- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Atserias, A. and Kolaitis, P. G. (2020). Consistency, acyclicity, and positive semirings. arXiv:2009.09488.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Ghrist, R. and Cooperband, Z. (2025). Obstructions to reality: torsors and visual paradox. arXiv:2507.01226.
- Lawvere, F. W. (1969). Diagonal arguments and Cartesian closed categories. *Lecture Notes in Mathematics* 92, 134–145.
- Vorob'ev, N. N. (1962). Consistent families of measures and their extensions. *Theory of Probability and Its Applications* 7, 147–163.
- *Cycles and Twists*; *Walls and Strategy*; *Four Levels of Obstruction in Social Choice* (drafts, this repository); *The Switch Between Fixed Point and No Fixed Point* (working note, this repository).
