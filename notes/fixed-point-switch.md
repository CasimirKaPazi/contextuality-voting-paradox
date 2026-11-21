# The Switch Between Fixed Point and No Fixed Point

*Working note, literature review before formulating one statement for the loops of* Cycles and Twists. *It collects results in which the same structure sometimes has a fixed point (a consistent global assignment) and sometimes not, and in which the switch between the two is itself a theorem. The results are cited; the reading that connects them is interpretation and is marked.*

## 1. The question

Locally, every context of a Condorcet cycle, of the Liar or of a strategic game has a consistent assignment. Globally there may be none. Lawvere's theorem describes one side of this switch: if the space of values has a map without a fixed point, self-reference through it is obstructed. The other side is equally a theorem: where every relevant map has a fixed point, self-reference is consistent (Kleene's recursion theorem, Scott, Brouwer, Kakutani). The question here is how the switch happens. Three mechanisms appear in the literature, and they are independent of one another.

## 2. First mechanism: loops in the cover

**Acyclic covers always glue.** Vorob'ev (1962) showed that every compatible family of probability distributions on a family of contexts extends to a global distribution exactly when the hypergraph of contexts is acyclic. Beeri, Fagin, Maier and Yannakakis (1983) proved the same for relations in databases, where acyclic schemes are exactly those in which pairwise consistency implies global consistency. Atserias and Kolaitis (2020) unified both for relations annotated in positive semirings. To show that every non-acyclic hypergraph admits a pairwise consistent but globally inconsistent family, they generalise Tseitin's construction, a parity constraint around a cycle, which is the form of the Liar. In contextuality, Vorob'ev's theorem says that contextuality needs a cycle in the compatibility structure (see the review of Budroni et al.).

**Simply connected spaces always aggregate.** Chichilnisky and Heal (1983) showed that a space of preferences admits a continuous, anonymous and unanimous aggregation rule for every number of voters exactly when it is contractible. Weinberger (2004) showed that one number of voters at least two already forces contractibility.

**Contextuality needs a non-trivial fundamental group.** Okay and Raussendorf (2020) proved that an arrangement of observables allows a parity-based contextuality proof only if the first homotopy group of its topological realisation is non-trivial.

*Reading.* All three say the same thing in different settings: without a loop there is no obstruction, and the first place an obstruction can live is around a loop. This is why the value-space results of *Cycles and Twists* concern a cycle, and why Rajsbaum and Raventós-Pujol's observation that contractibility is not the reason for Arrow's theorem matters. In the discrete, labelled setting, what happens around the loop is decided by the labels, not by the bare topology.

## 3. Second mechanism: going around twice

**Order-reversing maps and their squares.** A monotone map of a complete lattice has least and greatest fixed points (Tarski 1955). An order-reversing (antitone) map need not have any, but its square is monotone and does. Van Gelder's alternating fixpoint (1993) builds the semantics of logic programs with negation on exactly this: the transformation that defines stable models is antitone, and the composition of two passes is monotone. Its least fixed point is the well-founded partial model. Approximation fixpoint theory (Denecker, Marek and Truszczyński 2004) generalises this into one algebra of supported, Kripke–Kleene, stable and well-founded fixed points for non-monotone operators, covering logic programming, default logic and autoepistemic logic.

**Odd and even loops.** In logic programming and in Dung's argumentation frameworks the switch is visible as the parity of a cycle through negation or attack:
- A finite argumentation framework without a stable extension must contain an odd cycle (Dung 1995). In an odd cycle the labels in and out alternate on each circuit and cannot close up. This is the Liar.
- An even cycle has two stable extensions, and nothing in the framework chooses between them.
- The grounded extension, the least fixed point, leaves every argument of a cycle undecided.

Bench-Capon (2016) reads even cycles as dilemmas and odd cycles as paradoxes.

Dung's stable extensions are von Neumann and Morgenstern's stable sets, and his paper treats n-person games as an application.

**Truth.** Kripke (1975) obtained a consistent truth predicate as a fixed point of a monotone operator on three truth values, with the Liar in the gap. The revision theory of truth (Herzberger; Gupta and Belnap 1993) keeps two values and follows the revision sequence, in which the Liar oscillates with period two.

*Reading.* The trichotomy of *Where the Symmetry Goes* appears here exactly, in the parity of a loop through an order-reversing map:
- An odd loop has no fixed point: the paradox, placement (i).
- An even loop has two fixed points, and choosing one breaks a symmetry: placement (ii).
- The least fixed point in a three-valued space leaves the loop undecided: placement (iii), with the gap in the role of the lottery or of complete indifference.

**The majority graph as an argumentation framework.** Let each candidate attack every candidate it beats by majority, and let a tie be a mutual attack. Any two candidates are then in conflict, so a conflict-free set has at most one element. A stable extension is a single candidate that attacks everyone else, a (weak) Condorcet winner. The grounded extension contains the strict Condorcet winner if there is one and is empty otherwise. The three placements appear in this encoding without further assumptions:
- a Condorcet cycle is an odd cycle and has no stable extension, placement (i);
- two candidates tied with each other and beating the rest form a mutual attack, an even loop of length two, with two stable extensions that a tie-break must choose between, placement (ii);
- in both cases the grounded extension is empty, everything undecided, placement (iii) in its discrete form.

A tournament without a Condorcet winner contains a 3-cycle, which is Dung's theorem in this special case. *(The encoding is elementary and is checked here directly; no source treating it was found in this search.)*

Canning's hierarchy of rational algorithms (*Walls and Strategy*, Section 3) appears to be an instance of this mechanism. Rationality relative to a set of opponents is antitone, the odd and even stages behave like the two passes of an alternating fixpoint, and the absence of a largest closed set resembles the choice between the two stable models of an even loop. Canning's "imp" needs ties, which in the encoding above are exactly the even loops. The double cover of the Liar in *Cycles and Twists*, where going around once flips and twice restores, is the same mechanism in topological form.

## 4. Third mechanism: adding a value

**Partial functions turn the diagonal into a fixed point.** The diagonal argument and the recursion theorem use the same construction: if the diagonal sequence is one of the rows, the map acting on it has a fixed point; if it cannot be, the result is a contradiction (Owings 1973). Kleene's recursion theorem obtains the fixed point by admitting the everywhere undefined function, and Gaifman (2006) analyses the different ways of handling undefined values in this scheme ("gap logic"). Lawvere's theorem itself has both faces. Its contrapositive is the universal diagonal argument, and read directly it is a fixed-point theorem (Yanofsky 2003; Roberts 2021).

*Reading.* This is the exit by convexification in *Where the Symmetry Goes*, observation 4, seen from logic. The fixed point exists after a value is added that the original space lacked: undefined for programs, the gap for truth, the lottery or complete indifference for aggregation. The new value is fixed by the symmetry that had no fixed point before (negation of the gap is the gap; rotation of the uniform lottery is the uniform lottery).

## 5. What this suggests for a common statement

*(Interpretation.)* The three mechanisms answer three different questions about one loop:

1. **Is there a loop at all?** Without one, a global section always exists (Vorob'ev; Beeri et al.; Chichilnisky and Heal).
2. **What does going around it do?** Compose the constraints around the loop. The composite, the monodromy, acts on the values at the starting point, and a global section exists exactly when it has a fixed point. Each kind of edge gives a kind of monodromy:
   - an edge that flips (attack, negation) gives negation to the power of the length, so the parity of the length decides;
   - an edge that steps up (a strict order on a line) gives a shift that never has a fixed point, and the winding number counts it;
   - an edge that steps by less than half a turn on a circle allows a fixed point.
   The Condorcet cycle read as an attack graph (a candidate is accepted if no accepted candidate beats it) is an odd cycle with a parity obstruction; read as a placement on a line, it has a winding obstruction. The two readings differ in the edge map, not in the loop.
3. **Can the value space be enlarged?** Adding a value fixed by the monodromy (undefined, the gap, the uniform lottery) restores a fixed point.

Going around twice connects the second and third questions. The square of an order-reversing monodromy is monotone and always has fixed points; where the loop is even they are honest two-valued fixed points that must be chosen between, and where it is odd only the third value survives.

This suggests a form for a statement covering the Liar, the Condorcet cycle and the strategic diagonal: a loop of contexts, an edge map per context, and three cases (no fixed point, fixed points of the square only, a fixed point), with reduction mod 2 sending the shift on the integers to negation. The test is whether the diagonal of Lemma 2 in *Walls and Strategy* fits as an instance. The candidate reading: the strategist and the counter-programs form a loop of length two, and the composite "best reply to the counter-profile chosen against it" should have no fixed point exactly when the player has no dominant strategy. Whether this holds, and whether it holds for the rational diagonal of Proposition 4, is the first thing to check.

## 6. Questions

1. In a strict tournament every cycle of length four or more has chords, so the only even loops of the majority graph are ties. Are there encodings (for instance on rankings rather than candidates) in which longer even loops occur and the two stable extensions are related by a symmetry of the profile?
2. Tournament solutions (top cycle, uncovered set, Banks set) and argumentation semantics (grounded, preferred, stable) both assign acceptable sets to a dominance graph. Which tournament solutions are argumentation semantics of the majority graph, and does the alternating-fixpoint construction give a Condorcet-consistent rule with a natural ex ante reading?
3. Approximation fixpoint theory organises all fixed points of a non-monotone operator by approximations on pairs. Does Canning's hierarchy fit into it exactly, so that his set B* is a stable fixpoint in that theory?

## References

- Atserias, A. and Kolaitis, P. G. (2020). Consistency, acyclicity, and positive semirings. arXiv:2009.09488.
- Beeri, C., Fagin, R., Maier, D. and Yannakakis, M. (1983). On the desirability of acyclic database schemes. *Journal of the ACM* 30, 479–513.
- Bench-Capon, T. J. M. (2016). Dilemmas and paradoxes: cycles in argumentation frameworks. *Journal of Logic and Computation* 26, 1055–1064.
- Brandt, F., Brill, M. and Harrenstein, P. (2016). Tournament solutions. In *Handbook of Computational Social Choice*, Cambridge University Press.
- Budroni, C., Cabello, A., Gühne, O., Kleinmann, M. and Larsson, J.-Å. (2022). Kochen–Specker contextuality. *Reviews of Modern Physics* 94, 045007. arXiv:2102.13036.
- Canning, D. (1992). Rationality, computability, and Nash equilibrium. *Econometrica* 60, 877–888.
- Chichilnisky, G. and Heal, G. (1983). Necessary and sufficient conditions for a resolution of the social choice paradox. *Journal of Economic Theory* 31, 68–87.
- Denecker, M., Marek, V. and Truszczyński, M. (2004). Ultimate approximation and its application in nonmonotonic knowledge representation systems. *Information and Computation* 192, 84–121.
- Dung, P. M. (1995). On the acceptability of arguments and its fundamental role in nonmonotonic reasoning, logic programming and n-person games. *Artificial Intelligence* 77, 321–357.
- Gaifman, H. (2006). Naming and diagonalization, from Cantor to Gödel to Kleene. *Logic Journal of the IGPL* 14, 709–728.
- Gelfond, M. and Lifschitz, V. (1988). The stable model semantics for logic programming. *Proceedings of ICLP/SLP 1988*.
- Gupta, A. and Belnap, N. (1993). *The Revision Theory of Truth*. MIT Press.
- Kripke, S. (1975). Outline of a theory of truth. *Journal of Philosophy* 72, 690–716.
- Okay, C. and Raussendorf, R. (2020). Homotopical approach to quantum contextuality. *Quantum* 4, 217.
- Owings, J. C. (1973). Diagonalization and the recursion theorem. *Notre Dame Journal of Formal Logic* 14, 95–99.
- Roberts, D. M. (2021). Substructural fixed-point theorems and the diagonal argument: theme and variations. arXiv:2110.00239.
- Tarski, A. (1955). A lattice-theoretical fixpoint theorem and its applications. *Pacific Journal of Mathematics* 5, 285–309.
- Van Gelder, A. (1993). The alternating fixpoint of logic programs with negation. *Journal of Computer and System Sciences* 47, 185–221.
- Vorob'ev, N. N. (1962). Consistent families of measures and their extensions. *Theory of Probability and Its Applications* 7, 147–163.
- Weinberger, S. (2004). On the topological social choice model. *Journal of Economic Theory* 115, 377–384.
- Yanofsky, N. S. (2003). A universal approach to self-referential paradoxes, incompleteness and fixed points. *Bulletin of Symbolic Logic* 9, 362–386.
