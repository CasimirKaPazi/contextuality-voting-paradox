/-
  Proposition 4 of *Equivariant Obstructions*
  (`notes/equivariant-obstructions.md`, Section 3), without Gibbard's 1977
  theorem: for three alternatives and any finite set of voters, an
  SD-strategy-proof lottery rule that gives the common top at identical
  ballots has every degree in [0, 1].

  Encoding as in `ContextualFraction.lean`: profiles of the six rankings of
  `GlobalFormLottery` (abc, acb, cab, cba, bca, bac), a lottery at each
  profile, SD-SP for every voter's slice (`Model`), and the degree of voter i
  at a profile as the degree of the slice (`degAt`), the expected winding of
  *The Global Form*, Sections 4 and 7.

  Results:
  * `swap_fix` (the swap lemma of *The Global Form*, Section 7, for one voter):
    a step of the hexagon keeps the probability of the alternative it does not
    swap (`fixd`);
  * `deg_eq_of_fix`: two one-voter SD-SP lottery rules that differ only on one
    pair of alternatives, at every ranking, have the same degree;
  * `degAt_indep_sp`: the degree of an SD-SP lottery rule does not depend on
    the other voters' ballots. This is the statement of *The Global Form*,
    Section 7, that the real degree is a class for every SD-SP rule, here
    without Gibbard's theorem (`ContextualFraction.deg_indep` derives it from
    the theorem);
  * `prop4` (Proposition 4): with the common top at identical ballots
    (`UnanTop`), every degree lies in [0, 1].

  The proof of `deg_eq_of_fix` is the square of the note: a step of another
  voter changes the lotteries only on its pair, a step of voter i only on the
  pair of that step; where the pairs differ the changes are zero, and where
  they agree they telescope around the loop. The inequalities of `deg_pin`
  are the note's: with the others at abc, the lottery at abc and at acb is a
  for certain, and c has probability 0 at bca (`c_zero`, moving the other
  voters from bca through bac to abc, each step only raising a). They are
  closed by `linarith` from the SD-SP conditions at all pairs of rankings.
-/

module

public import Mathlib
public import ContextualFraction

@[expose] public section

open Finset GlobalFormLottery
open ContextualFraction (Prof LRule slice Lot SDSPn Model degAt lottery_slice)

namespace SPDegree

/-! ### One voter -/

/-- The alternative a step of the hexagon leaves in place: a at abc → acb,
    b at acb → cab, c at cab → cba, and so on. -/
def fixd : Fin 6 → Fin 3 := ![0, 1, 2, 0, 1, 2]

/-- **The swap lemma.** A step of the hexagon keeps the probability of the
    alternative it does not swap. -/
lemma swap_fix {f : Rule} (hL : Lottery f) (hS : SDSP f) (k : Fin 6) :
    f (k + 1) (fixd k) = f k (fixd k) := by
  obtain ⟨hn0, hs0⟩ := hL 0
  have l00 := hn0 0
  have l01 := hn0 1
  have l02 := hn0 2
  obtain ⟨hn1, hs1⟩ := hL 1
  have l10 := hn1 0
  have l11 := hn1 1
  have l12 := hn1 2
  obtain ⟨hn2, hs2⟩ := hL 2
  have l20 := hn2 0
  have l21 := hn2 1
  have l22 := hn2 2
  obtain ⟨hn3, hs3⟩ := hL 3
  have l30 := hn3 0
  have l31 := hn3 1
  have l32 := hn3 2
  obtain ⟨hn4, hs4⟩ := hL 4
  have l40 := hn4 0
  have l41 := hn4 1
  have l42 := hn4 2
  obtain ⟨hn5, hs5⟩ := hL 5
  have l50 := hn5 0
  have l51 := hn5 1
  have l52 := hn5 2
  obtain ⟨p01, q01⟩ : f 1 0 ≤ f 0 0 ∧ f 1 0 + f 1 1 ≤ f 0 0 + f 0 1 := hS 0 1
  obtain ⟨p02, q02⟩ : f 2 0 ≤ f 0 0 ∧ f 2 0 + f 2 1 ≤ f 0 0 + f 0 1 := hS 0 2
  obtain ⟨p03, q03⟩ : f 3 0 ≤ f 0 0 ∧ f 3 0 + f 3 1 ≤ f 0 0 + f 0 1 := hS 0 3
  obtain ⟨p04, q04⟩ : f 4 0 ≤ f 0 0 ∧ f 4 0 + f 4 1 ≤ f 0 0 + f 0 1 := hS 0 4
  obtain ⟨p05, q05⟩ : f 5 0 ≤ f 0 0 ∧ f 5 0 + f 5 1 ≤ f 0 0 + f 0 1 := hS 0 5
  obtain ⟨p10, q10⟩ : f 0 0 ≤ f 1 0 ∧ f 0 0 + f 0 2 ≤ f 1 0 + f 1 2 := hS 1 0
  obtain ⟨p12, q12⟩ : f 2 0 ≤ f 1 0 ∧ f 2 0 + f 2 2 ≤ f 1 0 + f 1 2 := hS 1 2
  obtain ⟨p13, q13⟩ : f 3 0 ≤ f 1 0 ∧ f 3 0 + f 3 2 ≤ f 1 0 + f 1 2 := hS 1 3
  obtain ⟨p14, q14⟩ : f 4 0 ≤ f 1 0 ∧ f 4 0 + f 4 2 ≤ f 1 0 + f 1 2 := hS 1 4
  obtain ⟨p15, q15⟩ : f 5 0 ≤ f 1 0 ∧ f 5 0 + f 5 2 ≤ f 1 0 + f 1 2 := hS 1 5
  obtain ⟨p20, q20⟩ : f 0 2 ≤ f 2 2 ∧ f 0 2 + f 0 0 ≤ f 2 2 + f 2 0 := hS 2 0
  obtain ⟨p21, q21⟩ : f 1 2 ≤ f 2 2 ∧ f 1 2 + f 1 0 ≤ f 2 2 + f 2 0 := hS 2 1
  obtain ⟨p23, q23⟩ : f 3 2 ≤ f 2 2 ∧ f 3 2 + f 3 0 ≤ f 2 2 + f 2 0 := hS 2 3
  obtain ⟨p24, q24⟩ : f 4 2 ≤ f 2 2 ∧ f 4 2 + f 4 0 ≤ f 2 2 + f 2 0 := hS 2 4
  obtain ⟨p25, q25⟩ : f 5 2 ≤ f 2 2 ∧ f 5 2 + f 5 0 ≤ f 2 2 + f 2 0 := hS 2 5
  obtain ⟨p30, q30⟩ : f 0 2 ≤ f 3 2 ∧ f 0 2 + f 0 1 ≤ f 3 2 + f 3 1 := hS 3 0
  obtain ⟨p31, q31⟩ : f 1 2 ≤ f 3 2 ∧ f 1 2 + f 1 1 ≤ f 3 2 + f 3 1 := hS 3 1
  obtain ⟨p32, q32⟩ : f 2 2 ≤ f 3 2 ∧ f 2 2 + f 2 1 ≤ f 3 2 + f 3 1 := hS 3 2
  obtain ⟨p34, q34⟩ : f 4 2 ≤ f 3 2 ∧ f 4 2 + f 4 1 ≤ f 3 2 + f 3 1 := hS 3 4
  obtain ⟨p35, q35⟩ : f 5 2 ≤ f 3 2 ∧ f 5 2 + f 5 1 ≤ f 3 2 + f 3 1 := hS 3 5
  obtain ⟨p40, q40⟩ : f 0 1 ≤ f 4 1 ∧ f 0 1 + f 0 2 ≤ f 4 1 + f 4 2 := hS 4 0
  obtain ⟨p41, q41⟩ : f 1 1 ≤ f 4 1 ∧ f 1 1 + f 1 2 ≤ f 4 1 + f 4 2 := hS 4 1
  obtain ⟨p42, q42⟩ : f 2 1 ≤ f 4 1 ∧ f 2 1 + f 2 2 ≤ f 4 1 + f 4 2 := hS 4 2
  obtain ⟨p43, q43⟩ : f 3 1 ≤ f 4 1 ∧ f 3 1 + f 3 2 ≤ f 4 1 + f 4 2 := hS 4 3
  obtain ⟨p45, q45⟩ : f 5 1 ≤ f 4 1 ∧ f 5 1 + f 5 2 ≤ f 4 1 + f 4 2 := hS 4 5
  obtain ⟨p50, q50⟩ : f 0 1 ≤ f 5 1 ∧ f 0 1 + f 0 0 ≤ f 5 1 + f 5 0 := hS 5 0
  obtain ⟨p51, q51⟩ : f 1 1 ≤ f 5 1 ∧ f 1 1 + f 1 0 ≤ f 5 1 + f 5 0 := hS 5 1
  obtain ⟨p52, q52⟩ : f 2 1 ≤ f 5 1 ∧ f 2 1 + f 2 0 ≤ f 5 1 + f 5 0 := hS 5 2
  obtain ⟨p53, q53⟩ : f 3 1 ≤ f 5 1 ∧ f 3 1 + f 3 0 ≤ f 5 1 + f 5 0 := hS 5 3
  obtain ⟨p54, q54⟩ : f 4 1 ≤ f 5 1 ∧ f 4 1 + f 4 0 ≤ f 5 1 + f 5 0 := hS 5 4
  fin_cases k <;> simp [fixd] <;> linarith

/-- Raising a over c at bca → bac does not raise c. -/
lemma step45 {f : Rule} (hL : Lottery f) (hS : SDSP f) : f 5 2 ≤ f 4 2 := by
  obtain ⟨_, s4⟩ := hL 4
  obtain ⟨_, s5⟩ := hL 5
  obtain ⟨_, q⟩ : f 4 1 ≤ f 5 1 ∧ f 4 1 + f 4 0 ≤ f 5 1 + f 5 0 := hS 5 4
  linarith

lemma fix50 {f : Rule} (hL : Lottery f) (hS : SDSP f) : f 0 2 = f 5 2 := by
  simpa [fixd] using swap_fix hL hS 5

/-- **Rules that differ on one pair have the same degree.** -/
lemma deg_eq_of_fix {f g : Rule} (hL : Lottery f) (hS : SDSP f) (hLg : Lottery g)
    (hSg : SDSP g) (z : Fin 3) (hz : ∀ r, g r z = f r z) : deg g = deg f := by
  have f0 : f 1 0 = f 0 0 := by simpa [fixd] using swap_fix hL hS 0
  have f1 : f 2 1 = f 1 1 := by simpa [fixd] using swap_fix hL hS 1
  have f2 : f 3 2 = f 2 2 := by simpa [fixd] using swap_fix hL hS 2
  have f3 : f 4 0 = f 3 0 := by simpa [fixd] using swap_fix hL hS 3
  have f4 : f 5 1 = f 4 1 := by simpa [fixd] using swap_fix hL hS 4
  have f5 : f 0 2 = f 5 2 := fix50 hL hS
  have g0 : g 1 0 = g 0 0 := by simpa [fixd] using swap_fix hLg hSg 0
  have g1 : g 2 1 = g 1 1 := by simpa [fixd] using swap_fix hLg hSg 1
  have g2 : g 3 2 = g 2 2 := by simpa [fixd] using swap_fix hLg hSg 2
  have g3 : g 4 0 = g 3 0 := by simpa [fixd] using swap_fix hLg hSg 3
  have g4 : g 5 1 = g 4 1 := by simpa [fixd] using swap_fix hLg hSg 4
  have g5 : g 0 2 = g 5 2 := fix50 hLg hSg
  have s0 := (hL 0).2
  have s1 := (hL 1).2
  have s2 := (hL 2).2
  have s3 := (hL 3).2
  have s4 := (hL 4).2
  have s5 := (hL 5).2
  have t0 := (hLg 0).2
  have t1 := (hLg 1).2
  have t2 := (hLg 2).2
  have t3 := (hLg 3).2
  have t4 := (hLg 4).2
  have t5 := (hLg 5).2
  have z0 := hz 0
  have z1 := hz 1
  have z2 := hz 2
  have z3 := hz 3
  have z4 := hz 4
  have z5 := hz 5
  have hz3 : z = 0 ∨ z = 1 ∨ z = 2 := by fin_cases z <;> simp
  unfold deg
  rcases hz3 with rfl | rfl | rfl <;> linarith

/-- **Pinning near the unanimous profile.** If the lottery at abc is a for
    certain and c has probability 0 at bca, the degree lies in [0, 1]. -/
lemma deg_pin {f : Rule} (hL : Lottery f) (hS : SDSP f) (h0 : f 0 0 = 1) (h4 : f 4 2 = 0) :
    0 ≤ deg f ∧ deg f ≤ 1 := by
  obtain ⟨hn0, hs0⟩ := hL 0
  have l00 := hn0 0
  have l01 := hn0 1
  have l02 := hn0 2
  obtain ⟨hn1, hs1⟩ := hL 1
  have l10 := hn1 0
  have l11 := hn1 1
  have l12 := hn1 2
  obtain ⟨hn2, hs2⟩ := hL 2
  have l20 := hn2 0
  have l21 := hn2 1
  have l22 := hn2 2
  obtain ⟨hn3, hs3⟩ := hL 3
  have l30 := hn3 0
  have l31 := hn3 1
  have l32 := hn3 2
  obtain ⟨hn4, hs4⟩ := hL 4
  have l40 := hn4 0
  have l41 := hn4 1
  have l42 := hn4 2
  obtain ⟨hn5, hs5⟩ := hL 5
  have l50 := hn5 0
  have l51 := hn5 1
  have l52 := hn5 2
  obtain ⟨p01, q01⟩ : f 1 0 ≤ f 0 0 ∧ f 1 0 + f 1 1 ≤ f 0 0 + f 0 1 := hS 0 1
  obtain ⟨p02, q02⟩ : f 2 0 ≤ f 0 0 ∧ f 2 0 + f 2 1 ≤ f 0 0 + f 0 1 := hS 0 2
  obtain ⟨p03, q03⟩ : f 3 0 ≤ f 0 0 ∧ f 3 0 + f 3 1 ≤ f 0 0 + f 0 1 := hS 0 3
  obtain ⟨p04, q04⟩ : f 4 0 ≤ f 0 0 ∧ f 4 0 + f 4 1 ≤ f 0 0 + f 0 1 := hS 0 4
  obtain ⟨p05, q05⟩ : f 5 0 ≤ f 0 0 ∧ f 5 0 + f 5 1 ≤ f 0 0 + f 0 1 := hS 0 5
  obtain ⟨p10, q10⟩ : f 0 0 ≤ f 1 0 ∧ f 0 0 + f 0 2 ≤ f 1 0 + f 1 2 := hS 1 0
  obtain ⟨p12, q12⟩ : f 2 0 ≤ f 1 0 ∧ f 2 0 + f 2 2 ≤ f 1 0 + f 1 2 := hS 1 2
  obtain ⟨p13, q13⟩ : f 3 0 ≤ f 1 0 ∧ f 3 0 + f 3 2 ≤ f 1 0 + f 1 2 := hS 1 3
  obtain ⟨p14, q14⟩ : f 4 0 ≤ f 1 0 ∧ f 4 0 + f 4 2 ≤ f 1 0 + f 1 2 := hS 1 4
  obtain ⟨p15, q15⟩ : f 5 0 ≤ f 1 0 ∧ f 5 0 + f 5 2 ≤ f 1 0 + f 1 2 := hS 1 5
  obtain ⟨p20, q20⟩ : f 0 2 ≤ f 2 2 ∧ f 0 2 + f 0 0 ≤ f 2 2 + f 2 0 := hS 2 0
  obtain ⟨p21, q21⟩ : f 1 2 ≤ f 2 2 ∧ f 1 2 + f 1 0 ≤ f 2 2 + f 2 0 := hS 2 1
  obtain ⟨p23, q23⟩ : f 3 2 ≤ f 2 2 ∧ f 3 2 + f 3 0 ≤ f 2 2 + f 2 0 := hS 2 3
  obtain ⟨p24, q24⟩ : f 4 2 ≤ f 2 2 ∧ f 4 2 + f 4 0 ≤ f 2 2 + f 2 0 := hS 2 4
  obtain ⟨p25, q25⟩ : f 5 2 ≤ f 2 2 ∧ f 5 2 + f 5 0 ≤ f 2 2 + f 2 0 := hS 2 5
  obtain ⟨p30, q30⟩ : f 0 2 ≤ f 3 2 ∧ f 0 2 + f 0 1 ≤ f 3 2 + f 3 1 := hS 3 0
  obtain ⟨p31, q31⟩ : f 1 2 ≤ f 3 2 ∧ f 1 2 + f 1 1 ≤ f 3 2 + f 3 1 := hS 3 1
  obtain ⟨p32, q32⟩ : f 2 2 ≤ f 3 2 ∧ f 2 2 + f 2 1 ≤ f 3 2 + f 3 1 := hS 3 2
  obtain ⟨p34, q34⟩ : f 4 2 ≤ f 3 2 ∧ f 4 2 + f 4 1 ≤ f 3 2 + f 3 1 := hS 3 4
  obtain ⟨p35, q35⟩ : f 5 2 ≤ f 3 2 ∧ f 5 2 + f 5 1 ≤ f 3 2 + f 3 1 := hS 3 5
  obtain ⟨p40, q40⟩ : f 0 1 ≤ f 4 1 ∧ f 0 1 + f 0 2 ≤ f 4 1 + f 4 2 := hS 4 0
  obtain ⟨p41, q41⟩ : f 1 1 ≤ f 4 1 ∧ f 1 1 + f 1 2 ≤ f 4 1 + f 4 2 := hS 4 1
  obtain ⟨p42, q42⟩ : f 2 1 ≤ f 4 1 ∧ f 2 1 + f 2 2 ≤ f 4 1 + f 4 2 := hS 4 2
  obtain ⟨p43, q43⟩ : f 3 1 ≤ f 4 1 ∧ f 3 1 + f 3 2 ≤ f 4 1 + f 4 2 := hS 4 3
  obtain ⟨p45, q45⟩ : f 5 1 ≤ f 4 1 ∧ f 5 1 + f 5 2 ≤ f 4 1 + f 4 2 := hS 4 5
  obtain ⟨p50, q50⟩ : f 0 1 ≤ f 5 1 ∧ f 0 1 + f 0 0 ≤ f 5 1 + f 5 0 := hS 5 0
  obtain ⟨p51, q51⟩ : f 1 1 ≤ f 5 1 ∧ f 1 1 + f 1 0 ≤ f 5 1 + f 5 0 := hS 5 1
  obtain ⟨p52, q52⟩ : f 2 1 ≤ f 5 1 ∧ f 2 1 + f 2 0 ≤ f 5 1 + f 5 0 := hS 5 2
  obtain ⟨p53, q53⟩ : f 3 1 ≤ f 5 1 ∧ f 3 1 + f 3 0 ≤ f 5 1 + f 5 0 := hS 5 3
  obtain ⟨p54, q54⟩ : f 4 1 ≤ f 5 1 ∧ f 4 1 + f 4 0 ≤ f 5 1 + f 5 0 := hS 5 4
  unfold deg
  constructor <;> linarith

/-! ### Any number of voters: the degree is a class -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- A step of another voter keeps voter i's degree. -/
lemma degAt_step {L : LRule ι} (hM : Model L) {i j : ι} (hij : i ≠ j) (π : Prof ι) :
    degAt L (Function.update π j (π j + 1)) i = degAt L π i := by
  unfold degAt
  apply deg_eq_of_fix (lottery_slice hM.1 π i) (hM.2 π i) (lottery_slice hM.1 _ i) (hM.2 _ i)
    (fixd (π j))
  intro r
  have h := swap_fix (lottery_slice hM.1 (Function.update π i r) j)
    (hM.2 (Function.update π i r) j) (π j)
  have e1 : Function.update (Function.update π j (π j + 1)) i r =
      Function.update (Function.update π i r) j (π j + 1) :=
    Function.update_comm hij.symm _ _ _
  have e2 : Function.update (Function.update π i r) j (π j) = Function.update π i r := by
    conv_lhs => rw [show π j = Function.update π i r j from (Function.update_of_ne hij.symm _ _).symm]
    exact Function.update_eq_self _ _
  unfold ContextualFraction.slice at h ⊢
  rw [e1]
  rw [e2] at h
  exact h

omit [Fintype ι] in
lemma degAt_succ {L : LRule ι} (hM : Model L) {i j : ι} (hij : i ≠ j) (π : Prof ι) (q : Fin 6) :
    degAt L (Function.update π j (q + 1)) i = degAt L (Function.update π j q) i := by
  have h := degAt_step hM hij (Function.update π j q)
  rwa [Function.update_self, Function.update_idem] at h

omit [Fintype ι] in
lemma degAt_upd {L : LRule ι} (hM : Model L) (i j : ι) (π : Prof ι) (p : Fin 6) :
    degAt L (Function.update π j p) i = degAt L π i := by
  by_cases hij : i = j
  · subst hij
    unfold degAt ContextualFraction.slice
    congr 1
    funext r
    rw [Function.update_idem]
  · have s0 := degAt_succ hM hij π 0
    have s1 := degAt_succ hM hij π 1
    have s2 := degAt_succ hM hij π 2
    have s3 := degAt_succ hM hij π 3
    have s4 := degAt_succ hM hij π 4
    have h0 : ∀ q : Fin 6, degAt L (Function.update π j q) i = degAt L (Function.update π j 0) i := by
      intro q
      fin_cases q
      exacts [rfl, s0, s1.trans s0, s2.trans (s1.trans s0), s3.trans (s2.trans (s1.trans s0)),
        s4.trans (s3.trans (s2.trans (s1.trans s0)))]
    have hc := h0 (π j)
    rw [Function.update_eq_self] at hc
    rw [h0 p, hc]

/-- **The degree is a class.** For an SD-SP lottery rule the degree of a voter
    does not depend on the other voters' ballots. -/
theorem degAt_indep_sp {L : LRule ι} (hM : Model L) (i : ι) (π π' : Prof ι) :
    degAt L π i = degAt L π' i := by
  have key : ∀ U : Finset ι, degAt L π i = degAt L (fun v => if v ∈ U then π' v else π v) i := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert j U _ ih =>
      rw [ih]
      have : (fun v => if v ∈ insert j U then π' v else π v) =
          Function.update (fun v => if v ∈ U then π' v else π v) j (π' j) := by
        funext v
        by_cases hvj : v = j
        · subst hvj
          simp
        · simp [hvj]
      rw [this, degAt_upd hM]
  simpa using key univ

/-! ### Proposition 4 -/

/-- The rule gives the common top at identical ballots. -/
def UnanTop (L : LRule ι) : Prop := ∀ r : Fin 6, L (fun _ => r) (top r) = 1

omit [Fintype ι] [DecidableEq ι] in
lemma others_zero {L : LRule ι} (hL : Lot L) {π : Prof ι} {x : Fin 3} (h : L π x = 1) (y : Fin 3)
    (hy : y ≠ x) : L π y = 0 := by
  obtain ⟨hn, hs⟩ := hL π
  have n0 := hn 0
  have n1 := hn 1
  have n2 := hn 2
  have hx3 : x = 0 ∨ x = 1 ∨ x = 2 := by fin_cases x <;> simp
  have hy3 : y = 0 ∨ y = 1 ∨ y = 2 := by fin_cases y <;> simp
  rcases hx3 with rfl | rfl | rfl <;> rcases hy3 with rfl | rfl | rfl <;>
    first | exact absurd rfl hy | linarith

/-- **c keeps probability 0** while voters move from bca through bac to abc:
    at every profile of bca, bac and abc ballots, c has probability 0. -/
theorem c_zero {L : LRule ι} (hM : Model L) (hU : UnanTop L) (t : Prof ι)
    (ht : ∀ v, t v = 4 ∨ t v = 5 ∨ t v = 0) : L t 2 = 0 := by
  have base : L (fun _ => 4) 2 = 0 := others_zero hM.1 (hU 4) 2 (by decide)
  have key : ∀ U : Finset ι, L (fun v => if v ∈ U then t v else 4) 2 = 0 := by
    intro U
    induction U using Finset.induction_on with
    | empty => simpa using base
    | @insert j U hj ih =>
      set σ : Prof ι := fun v => if v ∈ U then t v else 4 with hσ
      have hσj : σ j = 4 := by simp [hσ, hj]
      have hnew : (fun v => if v ∈ insert j U then t v else 4) = Function.update σ j (t j) := by
        funext v
        by_cases hvj : v = j
        · subst hvj
          simp
        · simp [hσ, hvj]
      have hLs := lottery_slice hM.1 σ j
      have hSs := hM.2 σ j
      have at4 : slice L σ j 4 2 = 0 := by
        unfold ContextualFraction.slice
        rw [← hσj, Function.update_eq_self]
        exact ih
      have at5 : slice L σ j 5 2 = 0 :=
        le_antisymm ((step45 hLs hSs).trans at4.le) ((hLs 5).1 2)
      rw [hnew]
      rcases ht j with h | h | h
      · rw [h]
        exact at4
      · rw [h]
        exact at5
      · rw [h]
        exact (fix50 hLs hSs).trans at5
  simpa using key univ

/-- **Proposition 4.** For an SD-SP lottery rule that gives the common top at
    identical ballots, every degree lies in [0, 1], at every profile. -/
theorem prop4 {L : LRule ι} (hM : Model L) (hU : UnanTop L) (π : Prof ι) (i : ι) :
    0 ≤ degAt L π i ∧ degAt L π i ≤ 1 := by
  rw [degAt_indep_sp hM i π (fun _ => 0)]
  apply deg_pin (lottery_slice hM.1 _ i) (hM.2 _ i)
  · show L (Function.update (fun _ => 0) i 0) 0 = 1
    rw [show Function.update (fun _ : ι => (0 : Fin 6)) i 0 = fun _ => 0 from
      Function.update_eq_self i _]
    exact hU 0
  · show L (Function.update (fun _ => 0) i 4) 2 = 0
    apply c_zero hM hU
    intro v
    by_cases hv : v = i
    · subst hv
      simp
    · simp [hv]

end SPDegree
