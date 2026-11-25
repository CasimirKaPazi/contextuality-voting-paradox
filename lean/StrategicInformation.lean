module

public import Mathlib

@[expose] public section

/-!
# Strategic information: virtual opponents, a finite corner, and the walk with memory

Statements from the working note *Strategic Information* (`notes/strategic-information.md`),
Sections 4b and 4c. `LeaderRule.lean` takes the best replies as definitions; this file derives
them from the valuation of ballots by ties, and adds the counting of Proposition 4.

Candidates form a finite type `A`, a voter's utilities are `u : A → ℝ`, and the weights of the
ties are `p : A → A → ℝ`, symmetric and non-negative, shared by all voters as part of the poll.
A ballot adds `s x` to the tally of `x`; its value is `val p u s`, the sum over ordered pairs of
`p x y (s x − s y)(u x − u y)` (twice the sum over unordered pairs in the note).

* **The value is linear** (`val_eq`): `val p u s = 2 ∑ x, s x · coef p u x`, with the coefficient
  `coef p u x = ∑ y, p x y (u x − u y)`. The coefficients sum to zero (`sum_coef`).
* **Proposition 5** (any weights).
  - The approval ballot `approveR`, approving exactly the candidates with a positive coefficient,
    is a best ballot among all ballots with entries in `[0, 1]` (`approval_best`), and the only
    best ballot with entries in `{0, 1}` when no coefficient vanishes (`approval_unique`).
    A coefficient is positive exactly when `u x` exceeds the mean of `u` under the weights
    `p x ·`, the virtual opponent (`coef_pos_iff`).
  - A plurality vote for `z` has the value `2 coef p u z` (`val_single`), so the best plurality
    votes maximise the coefficient; such a candidate has a positive coefficient unless all vanish,
    so it is approved (`plurality_approved`).
  - The opposite voter, with utility `−u`, has the opposite coefficients (`coef_neg`) and the
    complementary approval ballot (`approveR_neg`).
* **Proposition 6** (a finite corner). With `g` a lower bound on the utility differences of
  distinct candidates, `D` an upper bound on all utility differences, and `2 δ D < g`: a candidate
  whose tie with `z` outweighs its other ties by the factor `1/δ` has a positive coefficient
  exactly when it is preferred to `z` (`sign_coef`). Hence the best approval ballot is the leader
  rule (`prop6_approval`), and the preferred front-runner is the unique best plurality vote when
  every other candidate's ties weigh at most `δ` times the tie of the front-runners
  (`prop6_plurality`).
* **Proposition 4, the counting** (`walk_settles`, `settled_in`). A sequence of leaders `L : ℕ → A`
  in which every change brings a candidate that has not led before, and in which a leader kept for
  two rounds is kept for good, is constant from round `2 (|A| − 1)` on. If the leader stays in a
  set `S` once it is in it, and a leader changes within two rounds as long as no member of `S` has
  led, then the final leader is in `S`. The steps of `LeaderRule.lean` give these hypotheses for
  the walk with memory, with `S` the Smith set; the walk itself, with its tallies, is not built
  here.

Not formalised here: the bound for voters taken one by one when the corner condition fails for
some of them, and the computations.
-/

namespace StrategicInformation

open Finset

variable {A : Type*} [Fintype A]

/-! ### The value of a ballot -/

/-- The coefficient of candidate `x`: the value of one more vote for `x`. -/
def coef (p : A → A → ℝ) (u : A → ℝ) (x : A) : ℝ := ∑ y, p x y * (u x - u y)

/-- The value of a ballot `s`, summed over ordered pairs. -/
def val (p : A → A → ℝ) (u : A → ℝ) (s : A → ℝ) : ℝ :=
  ∑ x, ∑ y, p x y * (s x - s y) * (u x - u y)

theorem val_eq (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u s : A → ℝ) :
    val p u s = 2 * ∑ x, s x * coef p u x := by
  have h1 : ∀ x, ∑ y, p x y * (s x - s y) * (u x - u y)
      = s x * coef p u x - ∑ y, p x y * s y * (u x - u y) := by
    intro x
    unfold coef
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    ring
  have h2 : ∑ x, ∑ y, p x y * s y * (u x - u y) = -∑ x, s x * coef p u x := by
    rw [Finset.sum_comm, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    unfold coef
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rw [hp x y]
    ring
  unfold val
  rw [Finset.sum_congr rfl (fun x _ => h1 x), Finset.sum_sub_distrib, h2]
  ring

/-- The coefficients sum to zero. -/
theorem sum_coef (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u : A → ℝ) :
    ∑ x, coef p u x = 0 := by
  have h2 : (2 : ℝ) * ∑ x, coef p u x = 0 := by
    have h := val_eq p hp u (fun _ => 1)
    simp only [one_mul] at h
    rw [← h]
    simp [val]
  linarith

/-! ### Proposition 5: any weights -/

/-- The best approval ballot: approve exactly the candidates with a positive coefficient. -/
noncomputable def approveR (p : A → A → ℝ) (u : A → ℝ) (x : A) : ℝ :=
  if 0 < coef p u x then 1 else 0

theorem term_le (c s : ℝ) (hs : 0 ≤ s ∧ s ≤ 1) :
    s * c ≤ (if 0 < c then (1 : ℝ) else 0) * c := by
  split_ifs with h
  · nlinarith [mul_nonneg (sub_nonneg.mpr hs.2) h.le]
  · have hc : c ≤ 0 := not_lt.mp h
    nlinarith [mul_nonneg hs.1 (neg_nonneg.mpr hc)]

/-- The approval ballot is best among all ballots with entries in `[0, 1]`. -/
theorem approval_best (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u s : A → ℝ)
    (hs : ∀ x, 0 ≤ s x ∧ s x ≤ 1) : val p u s ≤ val p u (approveR p u) := by
  rw [val_eq p hp, val_eq p hp]
  have : ∑ x, s x * coef p u x ≤ ∑ x, approveR p u x * coef p u x :=
    Finset.sum_le_sum (fun x _ => term_le (coef p u x) (s x) (hs x))
  linarith

/-- With no vanishing coefficient, every other ballot with entries in `{0, 1}` is worse. -/
theorem approval_unique (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u s : A → ℝ)
    (hc : ∀ x, coef p u x ≠ 0) (hs : ∀ x, s x = 0 ∨ s x = 1) (hne : s ≠ approveR p u) :
    val p u s < val p u (approveR p u) := by
  rw [val_eq p hp, val_eq p hp]
  have hs' : ∀ x, 0 ≤ s x ∧ s x ≤ 1 := by
    intro x
    rcases hs x with h | h <;> rw [h] <;> norm_num
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hne
  have hlt : ∑ y, s y * coef p u y < ∑ y, approveR p u y * coef p u y := by
    apply Finset.sum_lt_sum (fun y _ => term_le (coef p u y) (s y) (hs' y))
    refine ⟨x, Finset.mem_univ x, ?_⟩
    unfold approveR at hx
    rcases lt_or_gt_of_ne (hc x) with h | h
    · have hn : ¬ 0 < coef p u x := not_lt.mpr h.le
      rw [ite_eq_right hn] at hx ⊢
      rcases hs x with h0 | h1
      · exact absurd h0 hx
      · rw [h1]; linarith
    · rw [ite_eq_left h] at hx ⊢
      rcases hs x with h0 | h1
      · rw [h0]; linarith
      · exact absurd h1 hx
  linarith

/-- The coefficient as a comparison with the virtual opponent: the weights `p x ·`. -/
theorem coef_eq (p : A → A → ℝ) (u : A → ℝ) (x : A) :
    coef p u x = (∑ y, p x y) * u x - ∑ y, p x y * u y := by
  unfold coef
  rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

/-- `x` is approved exactly when `u x` exceeds the weighted mean of the others' utilities. -/
theorem coef_pos_iff (p : A → A → ℝ) (u : A → ℝ) (x : A) :
    0 < coef p u x ↔ ∑ y, p x y * u y < (∑ y, p x y) * u x := by
  rw [coef_eq]
  constructor <;> intro h <;> linarith

/-- A plurality vote for `z` is worth twice the coefficient of `z`. -/
theorem val_single (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u : A → ℝ) [DecidableEq A]
    (z : A) : val p u (fun x => if x = z then 1 else 0) = 2 * coef p u z := by
  rw [val_eq p hp]
  congr 1
  simp [ite_mul]

/-- A best plurality vote is approved: its coefficient is positive unless all vanish. -/
theorem plurality_approved (p : A → A → ℝ) (hp : ∀ x y, p x y = p y x) (u : A → ℝ) {z : A}
    (hz : ∀ x, coef p u x ≤ coef p u z) (hnz : ∃ x, coef p u x ≠ 0) : 0 < coef p u z := by
  by_contra h
  push Not at h
  have hall : ∀ x ∈ (Finset.univ : Finset A), coef p u x ≤ 0 := fun x _ => (hz x).trans h
  have hzero := (Finset.sum_eq_zero_iff_of_nonpos hall).mp (sum_coef p hp u)
  obtain ⟨x, hx⟩ := hnz
  exact hx (hzero x (Finset.mem_univ x))

/-- The opposite voter has the opposite coefficients. -/
theorem coef_neg (p : A → A → ℝ) (u : A → ℝ) (x : A) :
    coef p (fun y => -u y) x = -coef p u x := by
  simp only [coef]
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

/-- The opposite voter casts the complementary approval ballot. -/
theorem approveR_neg (p : A → A → ℝ) (u : A → ℝ) (x : A) (hc : coef p u x ≠ 0) :
    approveR p (fun y => -u y) x = 1 - approveR p u x := by
  unfold approveR
  rw [coef_neg]
  rcases lt_or_gt_of_ne hc with h | h
  · have h1 : 0 < -coef p u x := by linarith
    have h2 : ¬ 0 < coef p u x := not_lt.mpr h.le
    rw [ite_eq_left h1, ite_eq_right h2]
    norm_num
  · have h1 : ¬ 0 < -coef p u x := not_lt.mpr (by linarith)
    rw [ite_eq_right h1, ite_eq_left h]
    norm_num

/-! ### Proposition 6: a finite corner -/

omit [Fintype A] in
theorem rest_bound (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) {D : ℝ}
    (hD : ∀ x y, |u x - u y| ≤ D) (x : A) (t : Finset A) :
    |∑ y ∈ t, p x y * (u x - u y)| ≤ (∑ y ∈ t, p x y) * D := by
  calc |∑ y ∈ t, p x y * (u x - u y)| ≤ ∑ y ∈ t, |p x y * (u x - u y)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ y ∈ t, p x y * D := by
        apply Finset.sum_le_sum
        intro y _
        rw [abs_mul, abs_of_nonneg (hp0 x y)]
        exact mul_le_mul_of_nonneg_left (hD x y) (hp0 x y)
    _ = (∑ y ∈ t, p x y) * D := by rw [Finset.sum_mul]

variable [DecidableEq A]

theorem coef_split (p : A → A → ℝ) (u : A → ℝ) (x z : A) :
    coef p u x = p x z * (u x - u z) + ∑ y ∈ Finset.univ.erase z, p x y * (u x - u y) := by
  unfold coef
  exact (Finset.add_sum_erase _ _ (Finset.mem_univ z)).symm

/-- The coefficient of `x` is its tie with `z`, up to `p x z · δ D`. -/
theorem coef_near (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) {D δ : ℝ}
    (hD : ∀ x y, |u x - u y| ≤ D) {x z : A}
    (hw : ∑ y ∈ Finset.univ.erase z, p x y ≤ δ * p x z) :
    |coef p u x - p x z * (u x - u z)| ≤ p x z * (δ * D) := by
  have hD0 : 0 ≤ D := by have := hD x x; simpa using this
  have hsplit : coef p u x - p x z * (u x - u z)
      = ∑ y ∈ Finset.univ.erase z, p x y * (u x - u y) := by
    rw [coef_split p u x z]
    ring
  rw [hsplit]
  calc _ ≤ (∑ y ∈ Finset.univ.erase z, p x y) * D := rest_bound p u hp0 hD x _
    _ ≤ (δ * p x z) * D := mul_le_mul_of_nonneg_right hw hD0
    _ = p x z * (δ * D) := by ring

/-- In the finite corner, the sign of a coefficient is decided by the main tie. -/
theorem sign_coef (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) {g D δ : ℝ}
    (hD : ∀ x y, |u x - u y| ≤ D) (hg : ∀ x y, x ≠ y → g ≤ |u x - u y|) (hδ : 0 ≤ δ)
    (hgap : 2 * δ * D < g) {x z : A} (hxz : x ≠ z) (hpxz : 0 < p x z)
    (hw : ∑ y ∈ Finset.univ.erase z, p x y ≤ δ * p x z) :
    0 < coef p u x ↔ u z < u x := by
  have hD0 : 0 ≤ D := by have := hD x x; simpa using this
  have hn := abs_le.mp (coef_near p u hp0 hD hw)
  have h2 : p x z * (2 * δ * D) < p x z * g := mul_lt_mul_of_pos_left hgap hpxz
  have hδD : 0 ≤ p x z * (δ * D) := mul_nonneg hpxz.le (mul_nonneg hδ hD0)
  have hgxz := hg x z hxz
  constructor
  · intro hc
    by_contra h
    push Not at h
    have h1 : g ≤ u z - u x := by
      rwa [abs_sub_comm, abs_of_nonneg (show (0 : ℝ) ≤ u z - u x by linarith)] at hgxz
    have h3 : p x z * g ≤ p x z * (u z - u x) := mul_le_mul_of_nonneg_left h1 hpxz.le
    linarith [hn.2]
  · intro h
    have h1 : g ≤ u x - u z := by
      rwa [abs_of_pos (show (0 : ℝ) < u x - u z by linarith)] at hgxz
    have h3 : p x z * g ≤ p x z * (u x - u z) := mul_le_mul_of_nonneg_left h1 hpxz.le
    linarith [hn.1]

/-- Proposition 6, approval: in the finite corner the best approval ballot is the leader rule. -/
theorem prop6_approval (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) {g D δ : ℝ}
    (hD : ∀ x y, |u x - u y| ≤ D) (hg : ∀ x y, x ≠ y → g ≤ |u x - u y|) (hδ : 0 ≤ δ)
    (hgap : 2 * δ * D < g) {a1 a2 : A} (h12 : a1 ≠ a2) (hp12 : 0 < p a1 a2)
    (hw1 : ∑ y ∈ Finset.univ.erase a2, p a1 y ≤ δ * p a1 a2)
    (hpa : ∀ x, x ≠ a1 → 0 < p x a1)
    (hw : ∀ x, x ≠ a1 → ∑ y ∈ Finset.univ.erase a1, p x y ≤ δ * p x a1) (x : A) :
    approveR p u x =
      if x = a1 then (if u a2 < u a1 then 1 else 0) else (if u a1 < u x then 1 else 0) := by
  unfold approveR
  by_cases hx : x = a1
  · rw [ite_eq_left hx, hx]
    have hs := sign_coef p u hp0 hD hg hδ hgap h12 hp12 hw1
    by_cases h : u a2 < u a1
    · rw [ite_eq_left (hs.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun hc => h (hs.mp hc)), ite_eq_right h]
  · rw [ite_eq_right hx]
    have hs := sign_coef p u hp0 hD hg hδ hgap hx (hpa x hx) (hw x hx)
    by_cases h : u a1 < u x
    · rw [ite_eq_left (hs.mpr h), ite_eq_left h]
    · rw [ite_eq_right (fun hc => h (hs.mp hc)), ite_eq_right h]

/-- The preferred front-runner `f` has the largest coefficient, strictly. -/
theorem front_runner_max (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y)
    (hsym : ∀ x y, p x y = p y x) {g D δ : ℝ} (hD : ∀ x y, |u x - u y| ≤ D)
    (hg : ∀ x y, x ≠ y → g ≤ |u x - u y|) (hδ : 0 ≤ δ) (hgap : 2 * δ * D < g) {f o : A}
    (hfo : f ≠ o) (hpfo : 0 < p f o)
    (hwf : ∑ y ∈ Finset.univ.erase o, p f y ≤ δ * p f o)
    (hwo : ∑ y ∈ Finset.univ.erase f, p o y ≤ δ * p f o)
    (hrest : ∀ x, x ≠ f → x ≠ o → ∑ y, p x y ≤ δ * p f o)
    (hpref : u o < u f) : ∀ x, x ≠ f → coef p u x < coef p u f := by
  have hD0 : 0 ≤ D := by have := hD f f; simpa using this
  have hg0 : 0 < g := by nlinarith [mul_nonneg hδ hD0]
  have hgfo : g ≤ u f - u o := by
    have := hg f o hfo
    rwa [abs_of_pos (show (0 : ℝ) < u f - u o by linarith)] at this
  have hnf := abs_le.mp (coef_near p u hp0 hD hwf)
  have hwo' : ∑ y ∈ Finset.univ.erase f, p o y ≤ δ * p o f := by rw [hsym o f]; exact hwo
  have hno := abs_le.mp (coef_near p u hp0 hD hwo')
  rw [hsym o f] at hno
  have h1 : p f o * g ≤ p f o * (u f - u o) := mul_le_mul_of_nonneg_left hgfo hpfo.le
  have h2 : p f o * (2 * δ * D) < p f o * g := mul_lt_mul_of_pos_left hgap hpfo
  have hpg : 0 < p f o * g := mul_pos hpfo hg0
  have hδD : 0 ≤ p f o * (δ * D) := mul_nonneg hpfo.le (mul_nonneg hδ hD0)
  have hcf : p f o * g - p f o * (δ * D) ≤ coef p u f := by linarith [hnf.1]
  intro x hxf
  by_cases hxo : x = o
  · rw [hxo]
    linarith [hno.2]
  · have hb : |coef p u x| ≤ (∑ y, p x y) * D := rest_bound p u hp0 hD x Finset.univ
    have h3 : (∑ y, p x y) * D ≤ (δ * p f o) * D :=
      mul_le_mul_of_nonneg_right (hrest x hxf hxo) hD0
    have h4 : coef p u x ≤ |coef p u x| := le_abs_self _
    have h5 : (δ * p f o) * D = p f o * (δ * D) := by ring
    linarith

/-- Proposition 6, plurality: in the finite corner the preferred front-runner is the unique best
    plurality vote. -/
theorem prop6_plurality (p : A → A → ℝ) (u : A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y)
    (hsym : ∀ x y, p x y = p y x) {g D δ : ℝ} (hD : ∀ x y, |u x - u y| ≤ D)
    (hg : ∀ x y, x ≠ y → g ≤ |u x - u y|) (hδ : 0 ≤ δ) (hgap : 2 * δ * D < g) {a1 a2 : A}
    (h12 : a1 ≠ a2) (hp12 : 0 < p a1 a2)
    (hw1 : ∑ y ∈ Finset.univ.erase a2, p a1 y ≤ δ * p a1 a2)
    (hw2 : ∑ y ∈ Finset.univ.erase a1, p a2 y ≤ δ * p a2 a1)
    (hrest : ∀ x, x ≠ a1 → x ≠ a2 → ∑ y, p x y ≤ δ * p a1 a2) :
    (u a2 < u a1 → ∀ x, x ≠ a1 → coef p u x < coef p u a1) ∧
      (u a1 < u a2 → ∀ x, x ≠ a2 → coef p u x < coef p u a2) := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  constructor
  · intro h
    have hw2' : ∑ y ∈ Finset.univ.erase a1, p a2 y ≤ δ * p a1 a2 := by
      rw [hsym a1 a2]; exact hw2
    exact front_runner_max p u hp0 hsym hD hg hδ hgap h12 hp12 hw1 hw2' hrest h
  · intro h
    have hp21 : 0 < p a2 a1 := by rw [hsym]; exact hp12
    have hw1' : ∑ y ∈ Finset.univ.erase a2, p a1 y ≤ δ * p a2 a1 := by
      rw [hsym a2 a1]; exact hw1
    have hrest' : ∀ x, x ≠ a2 → x ≠ a1 → ∑ y, p x y ≤ δ * p a2 a1 := by
      intro x hx2 hx1
      rw [hsym a2 a1]
      exact hrest x hx1 hx2
    exact front_runner_max p u hp0 hsym hD hg hδ hgap h21 hp21 hw2 hw1' hrest' h

/-! ### Proposition 4: the counting -/

section Counting

variable {B : Type*}


/-- The candidates that have led up to round `t`. -/
def led [DecidableEq B] (L : ℕ → B) (t : ℕ) : Finset B := (Finset.range (t + 1)).image L

/-- The leader is constant from round `t` on. -/
def ConstFrom (L : ℕ → B) (t : ℕ) : Prop := ∀ k, t ≤ k → L k = L t

theorem mem_led [DecidableEq B] (L : ℕ → B) {s t : ℕ} (h : s ≤ t) : L s ∈ led L t := by
  unfold led
  exact Finset.mem_image.mpr ⟨s, Finset.mem_range.mpr (by omega), rfl⟩

theorem led_mono [DecidableEq B] (L : ℕ → B) {s t : ℕ} (h : s ≤ t) : led L s ⊆ led L t := by
  intro a ha
  unfold led at ha ⊢
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ha
  have hr' := Finset.mem_range.mp hr
  exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr (by omega), rfl⟩

theorem led_card_succ [DecidableEq B] (L : ℕ → B)
    (hnew : ∀ t, L (t + 1) ≠ L t → L (t + 1) ∉ led L t)
    {t : ℕ} (h : L (t + 1) ≠ L t) : (led L t).card < (led L (t + 1)).card := by
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset (led_mono L (by omega : t ≤ t + 1))]
  exact ⟨L (t + 1), mem_led L le_rfl, hnew t h⟩

theorem change_within_two (L : ℕ → B)
    (hstay : ∀ t, L (t + 1) = L t → L (t + 1 + 1) = L t → ConstFrom L t) {t : ℕ}
    (h : ¬ ConstFrom L t) : L (t + 1) ≠ L t ∨ L (t + 1 + 1) ≠ L (t + 1) := by
  by_contra hc
  push Not at hc
  exact h (hstay t hc.1 (hc.2.trans hc.1))

theorem led_grows [DecidableEq B] (L : ℕ → B)
    (hnew : ∀ t, L (t + 1) ≠ L t → L (t + 1) ∉ led L t)
    (hstay : ∀ t, L (t + 1) = L t → L (t + 1 + 1) = L t → ConstFrom L t) :
    ∀ j : ℕ, ¬ ConstFrom L (2 * j) → j + 1 ≤ (led L (2 * j)).card
  | 0 => fun _ => by
      have h0 : 0 < (led L 0).card := Finset.card_pos.mpr ⟨L 0, mem_led L le_rfl⟩
      rw [Nat.mul_zero]
      omega
  | j + 1 => fun h => by
      have h' : ¬ ConstFrom L (2 * j) := by
        intro hc
        apply h
        intro k hk
        rw [hc k (by omega), hc (2 * (j + 1)) (by omega)]
      have ih := led_grows L hnew hstay j h'
      rcases change_within_two L hstay h' with hc | hc
      · have ha := led_card_succ L hnew hc
        have hb := Finset.card_le_card (led_mono L (show 2 * j + 1 ≤ 2 * (j + 1) by omega))
        omega
      · have ha := led_card_succ L hnew hc
        have hb := Finset.card_le_card (led_mono L (show 2 * j ≤ 2 * j + 1 by omega))
        have e : 2 * j + 1 + 1 = 2 * (j + 1) := by omega
        rw [e] at ha
        omega

/-- Proposition 4, part 4: the walk settles by round `2 (|A| − 1)`. -/
theorem walk_settles [Fintype B] [DecidableEq B] (L : ℕ → B)
    (hnew : ∀ t, L (t + 1) ≠ L t → L (t + 1) ∉ led L t)
    (hstay : ∀ t, L (t + 1) = L t → L (t + 1 + 1) = L t → ConstFrom L t) :
    ConstFrom L (2 * (Fintype.card B - 1)) := by
  by_contra h
  have hm : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨L 0⟩
  have hg := led_grows L hnew hstay _ h
  rcases change_within_two L hstay h with hc | hc
  · have ha := led_card_succ L hnew hc
    have hb := Finset.card_le_univ (led L (2 * (Fintype.card B - 1) + 1))
    omega
  · have ha := led_card_succ L hnew hc
    have hb := Finset.card_le_univ (led L (2 * (Fintype.card B - 1) + 1 + 1))
    have hc' := Finset.card_le_card
      (led_mono L (by omega : 2 * (Fintype.card B - 1) ≤ 2 * (Fintype.card B - 1) + 1))
    omega

/-- Proposition 4, part 5: if the leader stays in `S` once in it, and changes within two rounds
    as long as no member of `S` has led, the final leader is in `S`. -/
theorem settled_in (L : ℕ → B) (S : B → Prop) (hstayS : ∀ t, S (L t) → S (L (t + 1)))
    (hout : ∀ t, (∀ s, s ≤ t → ¬ S (L s)) → L (t + 1) ≠ L t ∨ L (t + 1 + 1) ≠ L (t + 1))
    {T : ℕ} (hT : ConstFrom L T) : S (L T) := by
  by_contra hS
  have hall : ∀ s, s ≤ T → ¬ S (L s) := by
    intro s hs hSs
    apply hS
    have hk : ∀ k, S (L (s + k)) := by
      intro k
      induction k with
      | zero => simpa using hSs
      | succ k ih => exact hstayS _ ih
    have := hk (T - s)
    rwa [show s + (T - s) = T by omega] at this
  rcases hout T hall with h | h
  · exact h (hT (T + 1) (by omega))
  · exact h ((hT (T + 1 + 1) (by omega)).trans (hT (T + 1) (by omega)).symm)

end Counting

end StrategicInformation
