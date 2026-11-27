# Covers and Division

*Working note. Proposition 1 of* Four Levels of Obstruction *shows that a scenario at the level of symmetry breaking becomes contextual when only symmetric objects are allowed: division turns level 3 into level 2. This note proves the converse for loops of contexts. Every empirical model of a loop is the division of a non-contextual model on a finite cover, and the cover is at level 3 for its group of deck transformations.*

*Precedent. The combinatorial core is known. Kharoof, Okay and Ipek (2024) characterise the contextual vertices of the non-signalling polytope of cycle scenarios with any finite outcome sets: they are exactly the "k-order cycle distributions" with k ≥ 2, which are the cycles of winding k used below. Since every model is a mixture of vertices, the decomposition of Proposition 2 follows from their theorem; the binary case is Kharoof, Ipek and Okay (2023), and the polytope of the binary n-cycle scenario goes back to Araújo, Quintino, Budroni, Terra Cunha and Cabello (2013). What is added here is an elementary proof by flow decomposition, which applies directly to arbitrary relations R_i, and the reading of the cycles as sections of covers, with the cover at level 3 for its deck group, so that the result becomes the converse of division. The cover reading was not found in these papers, which use simplicial homotopy instead. The script is an independent check. The readings at the end are interpretation.*

## 1. Loops and their covers

A loop has variables x₀, …, x_{n−1}, indices mod n, with x_i taking values in a set V_i, and contexts C_i = {x_i, x_{i+1}}, the context C_i allowing a relation R_i ⊆ V_i × V_{i+1} (*Loops of Relations*, Section 1). Throughout, n ≥ 3, so that two contexts share at most one variable. An **empirical model** is a probability distribution e_i on R_i for each i, such that the two contexts containing x_i give it the same marginal.

The **k-fold cover** is the loop of length kn with variables y₀, …, y_{kn−1}, the variable y_j taking values in V_{j mod n} and the context {y_j, y_{j+1}} allowing R_{j mod n}. The group ℤ/k acts on it by moving every index by n, a **deck transformation**, and it is a symmetry of the cover in the sense of *Four Levels*, Section 2. A global section of the k-fold cover is the loop run k times consistently, and its restriction to the first n variables need not close up: it closes up after k rounds.

**Proposition 1 (sections).** The global sections of the loop are exactly the global sections of the k-fold cover fixed by ℤ/k.

*Proof.* A section fixed by the shift by n is periodic with period n, so its first n values form a section of the loop; conversely a section of the loop, repeated k times, is a fixed section of the cover. ∎ *(Checked in Lean, `lean/Covers.lean`.)*

An empirical model on the cover that is fixed by ℤ/k **descends** to the loop: give the context C_i the distribution of any of its k lifts, which agree by symmetry. The result is an empirical model of the loop, since overlaps of lifted contexts lie over overlaps of contexts.

## 2. Every model of a loop comes from a cover

**Proposition 2.** Let the sets V_i be finite and m = min |V_i|. A family (e_i) is an empirical model of the loop exactly when it is a mixture of descents of the following models: for some k ≤ m and some global section s of the k-fold cover, the uniform mixture of the k sections obtained from s by the deck transformations. With K = lcm(1, …, m), every empirical model is the descent of one ℤ/K-invariant distribution over global sections of the K-fold cover.

The vertex form of this statement is the theorem of Kharoof, Okay and Ipek (2024) quoted above. A restricted relation R_i only sets some probabilities to zero, so its models form a face of the polytope with all pairs allowed, and the vertices of the face are vertices of the whole.

*Proof.* Form the layered graph with a node (i, v) for each i and each v in V_i, and an edge from (i, x) to (i + 1, y) of weight e_i(x, y) for each pair in R_i. Equal marginals at x_i say that the weight entering (i, v) from layer i − 1 equals the weight leaving it towards layer i + 1: the weights form a circulation. Every circulation on a finite graph is a non-negative combination of directed simple cycles (flow decomposition). A directed cycle in the layered graph advances one layer per edge, so it has length kn for some k ≥ 1, passes through each layer k times at distinct nodes (so k ≤ m), and its values, read along the cycle, form a global section s of the k-fold cover. A cycle carrying flow w passes k times through each context, so it contributes kw to the total weight of each context. As a model it is the descent of the uniform mixture of the k rotations of s, with mixture weight kw, since that mixture gives each of the cycle's k edges in each layer the weight 1/k. The weights kw add up to 1 because each e_i is a probability distribution. Conversely, a mixture of descents of invariant models is an empirical model. For the last statement, a section of the k-fold cover, run K/k times, is a section of the K-fold cover with the same descent. ∎ *(Checked in Lean, `lean/CoversDecomp.lean`, `prop2` and `prop2_lcm`. The decomposition there uses closed walks that close at the first repeated value at a layer with the fewest values, so k ≤ m; elsewhere they may pass a node more than once, and each walk is weighted by how often it uses an edge.)*

**Corollary (the converse of division).** Let the loop be finite.

1. It has an empirical model exactly when some finite cover has a global section.
2. If it is at level 2 (empirical models, no global section), then its K-fold cover is at level 3 relative to ℤ/K: global sections exist and none is symmetric. Its empirical models are exactly the divisions of this cover in the sense of *Four Levels*, Proposition 1, and their mixtures. The hidden variable is the round of the cover.
3. If it is at level 1, no finite cover has a global section.

*Proof.* (1) is Proposition 2 in one direction and descent in the other. In (2), sections of the cover exist by Proposition 2, a symmetric one would be a section of the loop by Proposition 1, and the models are the descents. (3) follows from (1). ∎ *(Checked in Lean, `lean/CoversDecomp.lean`: part 1 as `model_iff_cover`, for relations of period n; parts 2 and 3 as `cor_level2` and `cor_level1`, with the levels stated for loops and covers directly rather than through the general scenarios of `lean/Scenarios.lean`.)*

The possibilistic part of (1) is Proposition 1(c) of *Loops of Relations*: on finite value sets a possibilistically contextual loop has a section on some finite cover. Proposition 2 is its probabilistic form, and it identifies the cover as a symmetry-breaking scenario whose division is the loop. On infinite value sets the decomposition need not exist; the Condorcet cycle on the unbounded line, which has no section on any finite cover, has no probabilistic model either (*Four Levels*, Section 3).

**Examples** (`scripts/contextuality/loop_covers.py`).

- **The Liar on a triangle**, two contexts "equals" and one "is the negation of": every vertex of its polytope of models has winding 2. These are the sections of the double cover, true and false alternating round by round.
- **The CHSH scenario** is a loop of four contexts {A₀, B₀}, {B₀, A₁}, {A₁, B₁}, {B₁, A₀} with all outcomes allowed, and its models are the no-signalling boxes. The script finds 24 vertices: 16 of winding 1, the deterministic boxes, and 8 of winding 2, the PR boxes. So the PR boxes are Liar-type sections of the double cover, which matches Abramsky, Barbosa, Kishida, Lal and Mansfield (2015, Section 2): up to rearrangement, the Liar cycle of length 4 is the PR box. In the language of Kharoof, Okay and Ipek, these are the 2-order cycle distributions. On binary values a simple cycle winds at most twice, so for every n-cycle scenario with binary outcomes the extremal non-local boxes have winding exactly 2.
- **Random loops**, and loops built from bijections whose monodromy has no fixed point, with extra pairs added at random: every sampled vertex decomposes into cover sections, and where the loop has no section every cycle winds at least twice (largest winding found: 5).

## 3. Where the converse stops

**Arrow's scenario.** Its contexts are triples, not pairs around a loop, and the division in *Contextuality and Symmetry*, Section 2b, is by the voters' permutations, which do not act freely. A column of bits in which all voters agree is fixed by every permutation, so the quotient is not a cover in the sense above, and this is where the isotropy lemma of *Where the Symmetry Goes* enters. The converse holds there by Theorems 5 and 5′ (every model is a mixture of dictatorships), but by a different argument. Whether a common statement covers free and non-free divisions is open.

**Contexts beyond loops.** Contextuality needs a cycle somewhere: by Vorob'ev's theorem (1962), every consistent family of measures on a complex extends to a global one exactly when the complex is regular, which for scenarios means acyclic in the sense of hypergraphs. For a scenario whose contexts form a more general complex, the analogue of a finite cover is a covering of that complex, and a covering is trivial when the complex is simply connected. A contextual scenario on a simply connected complex would then be contextual in a way that no cover removes: contextuality at level 2 that is not the division of anything. Whether such scenarios exist in social choice, are open, and so is the relation to the cohomological obstructions of Abramsky, Mansfield and Barbosa, which use a first cohomology group: whether their classes are exactly the obstructions that some cover removes has not been checked. *Loops of Relations*, open question 2, asks the related question whether the levels reduce to loops.

**The electorate scenario.** At eight voters (three alternatives, joins only) the scenario has empirical models and no global section (*Consistency as an Extension Problem*, Section 3d). Its contexts are triples of electorates. Whether its models are divisions of a cover, and of which, is the test case for the previous paragraph.

## 4. Readings

*(Interpretation.)*

- **Naming removes the paradox on a loop.** A model of a contextual loop is consistent once the rounds are told apart. The paradox is not in the data but in identifying the k passes as one. This is the same move as naming the voters in Arrow's scenario, where the hidden variable is which voter decides. Here it is which round.
- **The paradox spread over time.** The k-fold cover is the loop run k times, and a section of it is a consistent history over k rounds. A model of the loop is the average over the rounds of such histories. On loops this makes exact the picture of a paradox that cannot be resolved at once but can be carried through time, with a definite state at every moment.
- **Two kinds of level 2.** Contextuality that some cover removes is symmetry breaking in disguise: the symmetry is the identification of the copies. Contextuality that survives every cover, if it exists in a given setting, is of another kind. The first kind is resolved by distinguishing perspectives, and the second would not be.

## 5. Open questions

1. A common form of Proposition 2 and of Theorems 5 and 5′: divisions by actions that are not free.
2. A contextual scenario of social choice on a simply connected complex of contexts, or a proof that there is none in a given class.
3. The electorate scenario at eight voters: is it the division of a cover?
4. Precedent for the cover reading. The vertex characterisation is in Kharoof, Okay and Ipek (2024); whether the identification of its cycle distributions with sections of covers, and of the cover with a symmetry-breaking scenario, is stated anywhere was not found.

## References

- Abramsky, S., Barbosa, R. S., Kishida, K., Lal, R. and Mansfield, S. (2015). Contextuality, cohomology and paradox. *24th EACSL Annual Conference on Computer Science Logic (CSL 2015)*, LIPIcs 41, 211–228. arXiv:1502.03097.
- Abramsky, S., Mansfield, S. and Barbosa, R. S. (2012). The cohomology of non-locality and contextuality. *Proceedings of the 8th International Workshop on Quantum Physics and Logic (QPL 2011)*, Electronic Proceedings in Theoretical Computer Science 95, 1–14. arXiv:1111.3620.
- Abramsky, S. and Brandenburger, A. (2011). The sheaf-theoretic structure of non-locality and contextuality. *New Journal of Physics* 13, 113036.
- Araújo, M., Quintino, M. T., Budroni, C., Terra Cunha, M. and Cabello, A. (2013). All noncontextuality inequalities for the n-cycle scenario. *Physical Review A* 88, 022118. arXiv:1206.3212.
- Kharoof, A., Ipek, S. and Okay, C. (2023). Topological methods for studying contextuality: N-cycle scenarios and beyond. *Entropy* 25, 1127. arXiv:2306.01459.
- Kharoof, A., Okay, C. and Ipek, S. (2024). Extremal simplicial distributions on cycle scenarios with arbitrary outcomes. arXiv:2406.19961.
- Vorob'ev, N. N. (1962). Consistent families of measures and their extensions. *Theory of Probability and its Applications* 7, 147–163.
