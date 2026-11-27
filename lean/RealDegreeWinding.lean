/-
  Section 4 of *The Global Form* (`notes/global-form.md`): the real degree is
  the expected winding of every compatible joint draw along the loop, and
  such joint draws exist when every step is compatible.

  Setting, as in `GlobalFormReal.lean`: the six rankings are the positions of
  the hexagon of `GlobalForm.lean`, a step of a loop flips one pair e, and a
  lottery is a function on the positions. Flipping e moves a ranking y to its
  partner (`partner e y`): one step forward on the hexagon if e is the pair
  of the edge after y, one step back if it is the pair of the edge before y,
  and nowhere for the two rankings at which flipping e would make a cycle.

  * `JointDraw e P Q J`: a joint law J of the rankings before and after a step
    flipping e, with marginals P and Q, in which each ranking stays or moves
    to its partner: the social ranking changes at most the comparison that
    the voter changes. Its expected displacement on the hexagon is
    `edisp J`.
  * `edisp_eq`: for every such joint draw the expected displacement is
    `GlobalFormReal.disp e P Q`, the note's formula over partner pairs: only
    the net flow between partners is fixed, and it is enough.
  * `Compatible e P Q`: before and after give the same law to the two
    comparisons the step leaves alone, that is the same mass to each ranking
    together with its partner. `exists_draw`: then a joint draw exists: keep
    min(P y, Q y) in place and move the excess to the partner.
  * `ewind_eq`, `exists_draws`: along a voter loop whose steps are all
    compatible, joint draws exist, and every family of them has expected
    winding `GlobalFormReal.rdeg`, the real degree.
-/

module

public import Mathlib
public import GlobalFormReal

@[expose] public section

open Finset GlobalForm GlobalFormReal

namespace RealDegreeWinding

/-! ### Partners and moves on the hexagon -/

/-- The partner of y under a flip of pair e (y itself if it has none). -/
def partner : Fin 3 → Fin 6 → Fin 6 :=
  ![![1, 0, 2, 4, 3, 5], ![0, 2, 1, 3, 5, 4], ![5, 1, 3, 2, 4, 0]]

/-- The partner is one step forward if e is the pair of the edge after y,
    one step back if it is the pair of the edge before, and y otherwise. -/
lemma partner_eq : ∀ e y, partner e y =
    if e = pairOf y then y + 1 else if e = pairOf (y - 1) then y - 1 else y := by decide

lemma partner_invol : ∀ e y, partner e (partner e y) = y := by decide

/-- Moving to the partner and moving back are the same edge. -/
lemma partner_symm : ∀ e y y', (y' = partner e y ∧ partner e y ≠ y) ↔
    (y = partner e y' ∧ partner e y' ≠ y') := by decide

/-- The displacement of a move from y to y' on the hexagon, as an integer. -/
def mvZ (y y' : Fin 6) : ℤ := if y' = y + 1 then 1 else if y' = y - 1 then -1 else 0

/-- The table of `mvZ`. -/
def mvT : Fin 6 → Fin 6 → ℤ :=
  ![![0, 1, 0, 0, 0, -1], ![-1, 0, 1, 0, 0, 0], ![0, -1, 0, 1, 0, 0],
    ![0, 0, -1, 0, 1, 0], ![0, 0, 0, -1, 0, 1], ![1, 0, 0, 0, -1, 0]]

lemma mvZ_tbl : ∀ y y', mvZ y y' = mvT y y' := by decide

/-- The table of `flipDir`. -/
def fdT : Fin 3 → Fin 6 → ℤ :=
  ![![1, -1, 0, 1, -1, 0], ![0, 1, -1, 0, 1, -1], ![-1, 0, 1, -1, 0, 1]]

lemma flipDir_tbl : ∀ e y, flipDir e y = fdT e y := by decide

/-! ### Joint draws of one step -/

/-- A joint law of the rankings before and after a step flipping e, with
    marginals P and Q, in which each ranking stays or moves to its partner. -/
structure JointDraw (e : Fin 3) (P Q : Fin 6 → ℝ) (J : Fin 6 → Fin 6 → ℝ) : Prop where
  nonneg : ∀ y y', 0 ≤ J y y'
  left : ∀ y, ∑ y', J y y' = P y
  right : ∀ y', ∑ y, J y y' = Q y'
  supp : ∀ y y', J y y' ≠ 0 → y' = y ∨ y' = partner e y

/-- The expected displacement of a joint draw on the hexagon. -/
noncomputable def edisp (J : Fin 6 → Fin 6 → ℝ) : ℝ := ∑ y, ∑ y', J y y' * (mvZ y y' : ℝ)

/-- **The lotteries fix the expected displacement.** For every joint draw of
    a step, the expected displacement is the note's formula over partner
    pairs. -/
theorem edisp_eq {e : Fin 3} {P Q : Fin 6 → ℝ} {J : Fin 6 → Fin 6 → ℝ}
    (hJ : JointDraw e P Q J) : edisp J = disp e P Q := by
  have z : ∀ y y', ¬ (y' = y ∨ y' = partner e y) → J y y' = 0 := fun y y' h => by
    by_contra hne
    exact h (hJ.supp y y' hne)
  have z00 := z 0 0
  have z01 := z 0 1
  have z02 := z 0 2
  have z03 := z 0 3
  have z04 := z 0 4
  have z05 := z 0 5
  have z10 := z 1 0
  have z11 := z 1 1
  have z12 := z 1 2
  have z13 := z 1 3
  have z14 := z 1 4
  have z15 := z 1 5
  have z20 := z 2 0
  have z21 := z 2 1
  have z22 := z 2 2
  have z23 := z 2 3
  have z24 := z 2 4
  have z25 := z 2 5
  have z30 := z 3 0
  have z31 := z 3 1
  have z32 := z 3 2
  have z33 := z 3 3
  have z34 := z 3 4
  have z35 := z 3 5
  have z40 := z 4 0
  have z41 := z 4 1
  have z42 := z 4 2
  have z43 := z 4 3
  have z44 := z 4 4
  have z45 := z 4 5
  have z50 := z 5 0
  have z51 := z 5 1
  have z52 := z 5 2
  have z53 := z 5 3
  have z54 := z 5 4
  have z55 := z 5 5
  have l0 := hJ.left 0
  have r0 := hJ.right 0
  have l1 := hJ.left 1
  have r1 := hJ.right 1
  have l2 := hJ.left 2
  have r2 := hJ.right 2
  have l3 := hJ.left 3
  have r3 := hJ.right 3
  have l4 := hJ.left 4
  have r4 := hJ.right 4
  have l5 := hJ.left 5
  have r5 := hJ.right 5
  unfold edisp disp
  simp only [Fin.sum_univ_six, mvZ_tbl, flipDir_tbl] at *
  fin_cases e <;> simp [partner, mvT, fdT] at z00 z01 z02 z03 z04 z05 z10 z11 z12 z13 z14 z15 z20 z21 z22 z23 z24 z25 z30 z31 z32 z33 z34 z35 z40 z41 z42 z43 z44 z45 z50 z51 z52 z53 z54 z55 ⊢ <;> linarith

/-- Compatibility of a step: the same mass to each ranking together with its
    partner, that is the same law of the two comparisons the step leaves
    alone. -/
def Compatible (e : Fin 3) (P Q : Fin 6 → ℝ) : Prop :=
  ∀ y, P y + P (partner e y) = Q y + Q (partner e y)

/-- The joint draw of a compatible step: keep min(P y, Q y) in place and
    move the excess of P over Q to the partner. -/
noncomputable def drawOf (e : Fin 3) (P Q : Fin 6 → ℝ) (y y' : Fin 6) : ℝ :=
  (if y' = y then min (P y) (Q y) else 0) +
    (if y' = partner e y ∧ partner e y ≠ y then max 0 (P y - Q y) else 0)

lemma min_add_max (a b : ℝ) : min a b + max 0 (a - b) = a := by
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    ring
  · rw [min_eq_right h, max_eq_right (by linarith)]
    ring

lemma min_add_max' {a b c d : ℝ} (h : a + c = b + d) : min a b + max 0 (c - d) = b := by
  rcases le_total a b with h' | h'
  · rw [min_eq_left h', max_eq_right (by linarith)]
    linarith
  · rw [min_eq_right h', max_eq_left (by linarith)]
    ring

/-- **Compatible steps have joint draws.** -/
theorem exists_draw {e : Fin 3} {P Q : Fin 6 → ℝ} (hP : ∀ y, 0 ≤ P y) (hQ : ∀ y, 0 ≤ Q y)
    (hc : Compatible e P Q) : JointDraw e P Q (drawOf e P Q) := by
  refine ⟨fun y y' => ?_, fun y => ?_, fun y' => ?_, fun y y' h => ?_⟩
  · unfold drawOf
    exact add_nonneg (by split_ifs <;> simp [hP y, hQ y]) (by split_ifs <;> simp)
  · unfold drawOf
    rw [sum_add_distrib, sum_ite_eq' univ y]
    simp only [mem_univ, ↓reduceIte]
    by_cases hz : partner e y = y
    · have hPQ : P y = Q y := by have := hc y; rw [hz] at this; linarith
      simp only [hz, ne_eq, not_true_eq_false, and_false, ↓reduceIte, sum_const_zero, add_zero]
      rw [hPQ, min_self]
    · simp only [hz, ne_eq, not_false_eq_true, and_true]
      rw [sum_ite_eq' univ (partner e y)]
      simp only [mem_univ, ↓reduceIte]
      exact min_add_max _ _
  · unfold drawOf
    rw [sum_add_distrib, sum_ite_eq univ y']
    simp only [mem_univ, ↓reduceIte]
    have hsw : ∀ y, (y' = partner e y ∧ partner e y ≠ y) ↔
        (y = partner e y' ∧ partner e y' ≠ y') := fun y => partner_symm e y y'
    simp only [hsw]
    by_cases hz : partner e y' = y'
    · have hPQ : P y' = Q y' := by have := hc y'; rw [hz] at this; linarith
      simp only [hz, ne_eq, not_true_eq_false, and_false, ↓reduceIte, sum_const_zero, add_zero]
      rw [hPQ, min_self]
    · simp only [hz, ne_eq, not_false_eq_true, and_true]
      rw [sum_ite_eq' univ (partner e y')]
      simp only [mem_univ, ↓reduceIte]
      exact min_add_max' (hc y')
  · unfold drawOf at h
    by_cases h1 : y' = y
    · exact Or.inl h1
    · by_cases h2 : y' = partner e y ∧ partner e y ≠ y
      · exact Or.inr h2.1
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero] at h
        exact absurd rfl h

/-! ### Along a voter loop -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Joint draws for the six steps of voter i's loop at context c. -/
def Draws (μ : (ι → Fin 6) → Fin 6 → ℝ) (i : ι) (c : ι → Fin 6)
    (J : Fin 6 → Fin 6 → Fin 6 → ℝ) : Prop :=
  ∀ k, JointDraw (pairOf k) (μ (setS {i} k c)) (μ (setS {i} (k + 1) c)) (J k)

/-- The expected winding of a family of joint draws: the expected
    displacement over the loop, divided by the six steps of a full turn. -/
noncomputable def ewind (J : Fin 6 → Fin 6 → Fin 6 → ℝ) : ℝ := (1 / 6) * ∑ k, edisp (J k)

omit [Fintype ι] in
/-- **The real degree is the expected winding** of every family of joint
    draws along the loop. -/
theorem ewind_eq {μ : (ι → Fin 6) → Fin 6 → ℝ} {i : ι} {c : ι → Fin 6}
    {J : Fin 6 → Fin 6 → Fin 6 → ℝ} (h : Draws μ i c J) : ewind J = rdeg μ i c := by
  unfold ewind rdeg
  rw [sum_congr rfl fun k _ => edisp_eq (h k)]

omit [Fintype ι] in
/-- **Joint draws exist** along a loop whose steps are all compatible. -/
theorem exists_draws {μ : (ι → Fin 6) → Fin 6 → ℝ} (h0 : ∀ π y, 0 ≤ μ π y) (i : ι)
    (c : ι → Fin 6)
    (hc : ∀ k, Compatible (pairOf k) (μ (setS {i} k c)) (μ (setS {i} (k + 1) c))) :
    ∃ J, Draws μ i c J :=
  ⟨fun k => drawOf (pairOf k) (μ (setS {i} k c)) (μ (setS {i} (k + 1) c)),
    fun k => exists_draw (h0 _) (h0 _) (hc k)⟩

end RealDegreeWinding
