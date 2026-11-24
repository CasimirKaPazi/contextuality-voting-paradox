module

public import Mathlib

@[expose] public section

/-!
# Joint draws from SD-strategy-proofness (Gibbard–Satterthwaite scenario, Proposition 1)

Working note *Gibbard–Satterthwaite as a Scenario*, Section 2.

One voter's slice of a random rule: the other voters' ballots are fixed, and `L σ` is the
lottery on the alternatives `α` when the voter reports the ranking `σ`. A ranking is an injective
map `σ : α → ℕ`; `σ a < σ b` means that `a` is ranked above `b`. Different maps may encode the same
ranking; the hypotheses below are stated for all encodings.

* `SDSP L`: for every truthful ranking `σ`, every report `τ` and every upper set `U` of `σ`, the
  report gives `U` at most the probability that the truthful ballot gives it.
* A *joint draw* for `σ` and `τ`: a joint distribution `J` with marginals `L σ` and `L τ`, supported
  on the admissible pairs `(a, b)`, those with `σ a ≤ σ b` and `τ b ≤ τ a`: with true preference
  `σ` the voter does not gain by reporting `τ`, and with true preference `τ` not by reporting `σ`.

`prop1`: a one-voter scheme with nonnegative lotteries is SD-strategy-proof exactly when every pair
of ballots admits a joint draw. In the scenario, a context changes one voter's ballot and keeps the
others, so applying `prop1` to every voter's slice gives the proposition for the whole rule.

Proof of the hard direction: a Markov kernel from `L σ` to `L τ` with admissible support, by
induction on the number of pairs on which `σ` and `τ` disagree. An adjacent pair of `σ` on which
they disagree is swapped; SD-strategy-proofness between the two neighbouring ballots moves mass
only from the upper to the lower element of the pair (`stepK`), and the kernels are composed.
-/

open Finset

namespace JointDraws

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- `U` is an upper set of the ranking `σ`. -/
def Up (σ : α → ℕ) (U : Finset α) : Prop := ∀ a b, b ∈ U → σ a < σ b → a ∈ U

/-- SD-strategy-proofness of a one-voter scheme. -/
def SDSP (L : (α → ℕ) → α → ℝ) : Prop :=
  ∀ σ τ : α → ℕ, Function.Injective σ → Function.Injective τ →
    ∀ U, Up σ U → ∑ a ∈ U, L τ a ≤ ∑ a ∈ U, L σ a

/-- A joint draw of `p` (at ballot `σ`) and `q` (at ballot `τ`) on admissible pairs. -/
def JointDraw (σ τ : α → ℕ) (p q : α → ℝ) : Prop :=
  ∃ J : α → α → ℝ, (∀ a b, 0 ≤ J a b) ∧ (∀ a, ∑ b, J a b = p a) ∧ (∀ b, ∑ a, J a b = q b) ∧
    (∀ a b, J a b ≠ 0 → σ a ≤ σ b ∧ τ b ≤ τ a)

/-! ### Easy direction -/

omit [DecidableEq α] in
theorem sd_of_joint {σ τ : α → ℕ} (hσ : Function.Injective σ) {p q : α → ℝ}
    (hJ : JointDraw σ τ p q) (U : Finset α) (hU : Up σ U) :
    ∑ b ∈ U, q b ≤ ∑ a ∈ U, p a := by
  obtain ⟨J, h0, hr, hc, hs⟩ := hJ
  have hz : ∀ a, a ∉ U → ∀ b ∈ U, J a b = 0 := by
    intro a ha b hb
    by_contra hne
    rcases lt_or_eq_of_le (hs a b hne).1 with h | h
    · exact ha (hU a b hb h)
    · exact ha (by rw [hσ h]; exact hb)
  calc ∑ b ∈ U, q b = ∑ b ∈ U, ∑ a, J a b := by simp_rw [hc]
    _ = ∑ a, ∑ b ∈ U, J a b := sum_comm
    _ = ∑ a ∈ U, ∑ b ∈ U, J a b :=
        (sum_subset (subset_univ U) (fun a _ ha => sum_eq_zero (hz a ha))).symm
    _ ≤ ∑ a ∈ U, ∑ b, J a b := by
        apply sum_le_sum
        intro a _
        exact sum_le_sum_of_subset_of_nonneg (subset_univ U) (fun b _ _ => h0 a b)
    _ = ∑ a ∈ U, p a := by simp_rw [hr]

/-! ### Threshold sets -/

/-- The alternatives ranked above position `t`. -/
def thr (σ : α → ℕ) (t : ℕ) : Finset α := univ.filter (fun a => σ a < t)

omit [DecidableEq α] in
lemma up_thr (σ : α → ℕ) (t : ℕ) : Up σ (thr σ t) := by
  intro a b hb hab
  simp only [thr, mem_filter, mem_univ, true_and] at hb ⊢
  omega

lemma thr_succ {σ : α → ℕ} (hσ : Function.Injective σ) (z : α) :
    thr σ (σ z + 1) = insert z (thr σ (σ z)) := by
  ext a
  simp only [thr, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    by_cases h' : σ a < σ z
    · exact Or.inr h'
    · exact Or.inl (hσ (by omega))
  · rintro (rfl | h) <;> omega

lemma sum_thr_succ {σ : α → ℕ} (hσ : Function.Injective σ) (f : α → ℝ) (z : α) :
    ∑ a ∈ thr σ (σ z + 1), f a = ∑ a ∈ thr σ (σ z), f a + f z := by
  have hz : z ∉ thr σ (σ z) := by simp [thr]
  rw [thr_succ hσ z, sum_insert hz]
  ring

/-! ### Swapping an adjacent pair -/

/-- The ranking `σ` with the positions of `x` and `y` exchanged. -/
def sw (σ : α → ℕ) (x y : α) : α → ℕ := fun a => σ (Equiv.swap x y a)

omit [Fintype α] in
lemma sw_x (σ : α → ℕ) (x y : α) : sw σ x y x = σ y := by simp [sw]

omit [Fintype α] in
lemma sw_y (σ : α → ℕ) (x y : α) : sw σ x y y = σ x := by simp [sw]

omit [Fintype α] in
lemma sw_other (σ : α → ℕ) {x y a : α} (h1 : a ≠ x) (h2 : a ≠ y) : sw σ x y a = σ a := by
  simp [sw, Equiv.swap_apply_of_ne_of_ne h1 h2]

omit [Fintype α] in
lemma sw_inj {σ : α → ℕ} (hσ : Function.Injective σ) (x y : α) :
    Function.Injective (sw σ x y) := by
  intro a b h
  unfold sw at h
  exact (Equiv.swap x y).injective (hσ h)

omit [Fintype α] in
/-- The three cases for an alternative under a swap, as statements about numbers. -/
lemma sw_cases (σ τ : α → ℕ) (hσ : Function.Injective σ) (x y a : α) :
    (σ a = σ x ∧ τ a = τ x ∧ sw σ x y a = σ y) ∨ (σ a = σ y ∧ τ a = τ y ∧ sw σ x y a = σ x) ∨
      (σ a ≠ σ x ∧ σ a ≠ σ y ∧ sw σ x y a = σ a) := by
  by_cases h1 : a = x
  · left; rw [h1]; exact ⟨rfl, rfl, sw_x σ x y⟩
  · by_cases h2 : a = y
    · right; left; rw [h2]; exact ⟨rfl, rfl, sw_y σ x y⟩
    · right; right
      exact ⟨fun e => h1 (hσ e), fun e => h2 (hσ e), sw_other σ h1 h2⟩

/-- Away from the swapped positions the threshold sets do not change. -/
lemma thr_sw {σ : α → ℕ} {x y : α} (hxy : σ x < σ y) {t : ℕ} (ht : t ≤ σ x ∨ σ y < t) :
    thr (sw σ x y) t = thr σ t := by
  ext a
  simp only [thr, mem_filter, mem_univ, true_and]
  by_cases h1 : a = x
  · rw [h1, sw_x]; constructor <;> intro <;> omega
  · by_cases h2 : a = y
    · rw [h2, sw_y]; constructor <;> intro <;> omega
    · rw [sw_other σ h1 h2]

lemma thr_pair {σ : α → ℕ} (hσ : Function.Injective σ) {x y : α} (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) :
    thr σ (σ y + 1) = insert y (insert x (thr σ (σ x))) := by
  ext a
  simp only [thr, mem_filter, mem_univ, true_and, mem_insert]
  constructor
  · intro h
    by_cases hay : a = y
    · exact Or.inl hay
    by_cases hax : a = x
    · exact Or.inr (Or.inl hax)
    have h1 : σ a ≠ σ y := fun e => hay (hσ e)
    have h2 : σ a ≠ σ x := fun e => hax (hσ e)
    have h3 := hadj a
    right; right; omega
  · rintro (rfl | rfl | h) <;> omega

lemma sum_thr_pair {σ : α → ℕ} (hσ : Function.Injective σ) {x y : α} (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) (f : α → ℝ) :
    ∑ a ∈ thr σ (σ y + 1), f a = ∑ a ∈ thr σ (σ x), f a + f x + f y := by
  have hyx : y ∉ insert x (thr σ (σ x)) := by
    simp only [mem_insert, thr, mem_filter, mem_univ, true_and, not_or]
    exact ⟨fun h => by rw [h] at hxy; exact lt_irrefl _ hxy, by omega⟩
  have hx : x ∉ thr σ (σ x) := by simp [thr]
  rw [thr_pair hσ hxy hadj, sum_insert hyx, sum_insert hx]
  ring

/-! ### What SD-strategy-proofness says about an adjacent swap -/

section Step

variable {L : (α → ℕ) → α → ℝ} {σ : α → ℕ} {x y : α}

lemma sum_sw_eq (hsd : SDSP L) (hσ : Function.Injective σ) (hxy : σ x < σ y) {t : ℕ}
    (ht : t ≤ σ x ∨ σ y < t) :
    ∑ a ∈ thr σ t, L (sw σ x y) a = ∑ a ∈ thr σ t, L σ a := by
  apply le_antisymm (hsd σ (sw σ x y) hσ (sw_inj hσ x y) _ (up_thr σ t))
  have h := hsd (sw σ x y) σ (sw_inj hσ x y) hσ _ (up_thr (sw σ x y) t)
  rwa [thr_sw hxy ht] at h

lemma step_other (hsd : SDSP L) (hσ : Function.Injective σ) (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) {z : α} (hzx : z ≠ x) (hzy : z ≠ y) :
    L (sw σ x y) z = L σ z := by
  have h1 : σ z ≠ σ x := fun e => hzx (hσ e)
  have h2 : σ z ≠ σ y := fun e => hzy (hσ e)
  have h3 := hadj z
  have eA := sum_sw_eq hsd hσ hxy (t := σ z + 1) (by omega)
  have eB := sum_sw_eq hsd hσ hxy (t := σ z) (by omega)
  rw [sum_thr_succ hσ (L (sw σ x y)) z, sum_thr_succ hσ (L σ) z, eB] at eA
  linarith

lemma step_x (hsd : SDSP L) (hσ : Function.Injective σ) (hxy : σ x < σ y) :
    L (sw σ x y) x ≤ L σ x := by
  have h := hsd σ (sw σ x y) hσ (sw_inj hσ x y) _ (up_thr σ (σ x + 1))
  have eB := sum_sw_eq hsd hσ hxy (t := σ x) (Or.inl le_rfl)
  rw [sum_thr_succ hσ (L (sw σ x y)) x, sum_thr_succ hσ (L σ) x, eB] at h
  linarith

lemma step_pair (hsd : SDSP L) (hσ : Function.Injective σ) (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) :
    L (sw σ x y) x + L (sw σ x y) y = L σ x + L σ y := by
  have eA := sum_sw_eq hsd hσ hxy (t := σ y + 1) (Or.inr (Nat.lt_succ_self _))
  have eB := sum_sw_eq hsd hσ hxy (t := σ x) (Or.inl le_rfl)
  rw [sum_thr_pair hσ hxy hadj (L (sw σ x y)), sum_thr_pair hσ hxy hadj (L σ), eB] at eA
  linarith

end Step

/-! ### The kernel of one swap -/

noncomputable def ratio (p q : ℝ) : ℝ := if p = 0 then 1 else q / p

lemma ratio_bounds {p q : ℝ} (hq : 0 ≤ q) (hqp : q ≤ p) :
    0 ≤ ratio p q ∧ ratio p q ≤ 1 ∧ p * ratio p q = q := by
  unfold ratio
  split_ifs with h
  · refine ⟨zero_le_one, le_rfl, ?_⟩
    rw [h] at hqp ⊢
    linarith
  · have hp : 0 < p := lt_of_le_of_ne (le_trans hq hqp) (Ne.symm h)
    refine ⟨div_nonneg hq hp.le, (div_le_one hp).mpr hqp, ?_⟩
    field_simp

/-- Keep every outcome, except that `x` stays with probability `r` and moves to `y` otherwise. -/
noncomputable def stepK (r : ℝ) (x y a b : α) : ℝ :=
  (if a = b then 1 else 0) +
    (if a = x then (if b = x then r - 1 else 0) + (if b = y then 1 - r else 0) else 0)

section Kernel

variable {x y : α}

omit [Fintype α] in
lemma stepK_nonneg (hne : x ≠ y) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a b : α) :
    0 ≤ stepK r x y a b := by
  unfold stepK
  by_cases hax : a = x
  · rw [hax]
    by_cases hbx : b = x
    · rw [hbx]; simp [hne]; linarith
    · by_cases hby : b = y
      · rw [hby]; simp [hne, Ne.symm hne]; linarith
      · simp [hbx, hby, Ne.symm hbx]
  · by_cases hab : a = b
    · rw [hab] at hax ⊢; simp [hax]
    · simp [hax, hab]

lemma stepK_row (_hne : x ≠ y) (r : ℝ) (a : α) : ∑ b, stepK r x y a b = 1 := by
  unfold stepK
  rw [sum_add_distrib]
  by_cases h : a = x
  · simp [h, sum_add_distrib]
  · simp [h]

lemma stepK_col_x (hne : x ≠ y) (p : α → ℝ) (r : ℝ) :
    ∑ a, p a * stepK r x y a x = p x * r := by
  have key : ∀ a, p a * stepK r x y a x = if a = x then p x * r else 0 := by
    intro a
    unfold stepK
    by_cases h : a = x
    · rw [h]; simp [hne]
    · simp [h]
  rw [sum_congr rfl (fun a _ => key a)]
  simp

lemma stepK_col_y (hne : x ≠ y) (p : α → ℝ) (r : ℝ) :
    ∑ a, p a * stepK r x y a y = p y + p x * (1 - r) := by
  have key : ∀ a, p a * stepK r x y a y =
      (if a = y then p y else 0) + (if a = x then p x * (1 - r) else 0) := by
    intro a
    unfold stepK
    by_cases hx : a = x
    · rw [hx]; simp [hne, Ne.symm hne]
    · by_cases hy : a = y
      · rw [hy]; simp [Ne.symm hne]
      · simp [hx, hy]
  rw [sum_congr rfl (fun a _ => key a), sum_add_distrib]
  simp

lemma stepK_col_o (p : α → ℝ) (r : ℝ) {b : α} (hbx : b ≠ x) (hby : b ≠ y) :
    ∑ a, p a * stepK r x y a b = p b := by
  have key : ∀ a, p a * stepK r x y a b = if a = b then p a else 0 := by
    intro a
    unfold stepK
    by_cases h : a = x
    · rw [h]; simp [hbx, hby, Ne.symm hbx]
    · by_cases hab : a = b
      · rw [hab]; simp [hbx]
      · simp [h, hab]
  rw [sum_congr rfl (fun a _ => key a)]
  simp

omit [Fintype α] in
lemma stepK_supp (r : ℝ) (a b : α) (h : stepK r x y a b ≠ 0) : a = b ∨ (a = x ∧ b = y) := by
  by_contra hc
  push Not at hc
  obtain ⟨hab, hxy'⟩ := hc
  apply h
  unfold stepK
  by_cases hax : a = x
  · have hby : b ≠ y := hxy' hax
    rw [hax] at hab ⊢
    simp [hab, Ne.symm hab, hby]
  · simp [hab, hax]

end Kernel

/-! ### Composition of kernels -/

/-- Composition of two kernels. -/
def kcomp (K1 K2 : α → α → ℝ) (a c : α) : ℝ := ∑ b, K1 a b * K2 b c

/-! ### Disagreements and adjacent disagreements -/

/-- The ordered pairs on which `σ` and `τ` disagree. -/
def invs (σ τ : α → ℕ) : Finset (α × α) :=
  univ.filter (fun p => σ p.1 < σ p.2 ∧ τ p.2 < τ p.1)

omit [DecidableEq α] in
/-- A disagreement gives one between neighbours of `σ`. -/
lemma exists_adj {σ τ : α → ℕ} : ∀ (d : ℕ) (a b : α), σ b - σ a = d → σ a < σ b → τ b < τ a →
    ∃ x y, σ x < σ y ∧ (∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) ∧ τ y < τ x := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro a b hd hab hτ
    by_cases hadj : ∀ c, ¬ (σ a < σ c ∧ σ c < σ b)
    · exact ⟨a, b, hab, hadj, hτ⟩
    · push Not at hadj
      obtain ⟨c, hac, hcb⟩ := hadj
      by_cases hca : τ c < τ a
      · exact ih (σ c - σ a) (by omega) a c rfl hac hca
      · exact ih (σ b - σ c) (by omega) c b rfl hcb (by omega)

section Swap

variable {σ τ : α → ℕ} {x y : α}

/-- A disagreement after the swap is one before it, in the same order. -/
lemma inv_sub (hσ : Function.Injective σ) (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) (hyx : τ y < τ x) {a b : α}
    (h1 : sw σ x y a < sw σ x y b) (h2 : τ b < τ a) : σ a < σ b := by
  have ha := sw_cases σ τ hσ x y a
  have hb := sw_cases σ τ hσ x y b
  have hadja := hadj a
  have hadjb := hadj b
  rcases ha with ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ | ⟨a1, a2, a3⟩ <;>
    rcases hb with ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ | ⟨b1, b2, b3⟩ <;> omega

lemma invs_sw_ssubset (hσ : Function.Injective σ) (hxy : σ x < σ y)
    (hadj : ∀ c, ¬ (σ x < σ c ∧ σ c < σ y)) (hyx : τ y < τ x) :
    invs (sw σ x y) τ ⊂ invs σ τ := by
  have hsub : invs (sw σ x y) τ ⊆ invs σ τ := by
    intro p hp
    simp only [invs, mem_filter, mem_univ, true_and] at hp ⊢
    exact ⟨inv_sub hσ hxy hadj hyx hp.1 hp.2, hp.2⟩
  refine (ssubset_iff_of_subset hsub).mpr ⟨(x, y), ?_, ?_⟩
  · simp only [invs, mem_filter, mem_univ, true_and]
    exact ⟨hxy, hyx⟩
  · intro h
    simp only [invs, mem_filter, mem_univ, true_and, sw_x, sw_y] at h
    omega

end Swap

/-- Without disagreements the two ballots get the same lottery. -/
lemma eq_of_noinv {L : (α → ℕ) → α → ℝ} (hsd : SDSP L) {σ τ : α → ℕ}
    (hσ : Function.Injective σ) (hτ : Function.Injective τ)
    (h0 : ∀ a b, ¬ (σ a < σ b ∧ τ b < τ a)) (z : α) : L τ z = L σ z := by
  have hup : ∀ t, Up τ (thr σ t) := by
    intro t a b hb hab
    simp only [thr, mem_filter, mem_univ, true_and] at hb ⊢
    by_contra hc
    exact h0 b a ⟨by omega, hab⟩
  have e : ∀ t, ∑ a ∈ thr σ t, L τ a = ∑ a ∈ thr σ t, L σ a := fun t =>
    le_antisymm (hsd σ τ hσ hτ _ (up_thr σ t)) (hsd τ σ hτ hσ _ (hup t))
  have h1 := e (σ z + 1)
  rw [sum_thr_succ hσ (L τ) z, sum_thr_succ hσ (L σ) z, e (σ z)] at h1
  linarith

/-! ### The kernel along a path of swaps -/

theorem kernel_exists {L : (α → ℕ) → α → ℝ} (hL0 : ∀ σ a, 0 ≤ L σ a) (hsd : SDSP L) :
    ∀ (n : ℕ) (σ τ : α → ℕ), (invs σ τ).card = n → Function.Injective σ →
      Function.Injective τ →
      ∃ K : α → α → ℝ, (∀ a b, 0 ≤ K a b) ∧ (∀ a, ∑ b, K a b = 1) ∧
        (∀ b, ∑ a, L σ a * K a b = L τ b) ∧ (∀ a b, K a b ≠ 0 → σ a ≤ σ b ∧ τ b ≤ τ a) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro σ τ hn hσ hτ
    by_cases h0 : ∀ a b, ¬ (σ a < σ b ∧ τ b < τ a)
    · -- no disagreement: the identity kernel
      refine ⟨fun a b => if a = b then 1 else 0, ?_, ?_, ?_, ?_⟩
      · intro a b
        by_cases h : a = b <;> simp [h]
      · intro a
        simp
      · intro b
        simp [eq_of_noinv hsd hσ hτ h0 b]
      · intro a b h
        by_cases hab : a = b
        · rw [hab]; exact ⟨le_rfl, le_rfl⟩
        · simp [hab] at h
    · push Not at h0
      obtain ⟨a₀, b₀, hab₀, hba₀⟩ := h0
      obtain ⟨x, y, hxy, hadj, hyx⟩ := exists_adj (σ b₀ - σ a₀) a₀ b₀ rfl hab₀ hba₀
      have hne : x ≠ y := fun h => by rw [h] at hxy; exact lt_irrefl _ hxy
      have hσ' : Function.Injective (sw σ x y) := sw_inj hσ x y
      have hlt : (invs (sw σ x y) τ).card < n := by
        rw [← hn]; exact card_lt_card (invs_sw_ssubset hσ hxy hadj hyx)
      obtain ⟨K2, h2n, h2r, h2c, h2s⟩ := ih _ hlt (sw σ x y) τ rfl hσ' hτ
      obtain ⟨r, hr0, hr1, hrm⟩ : ∃ r, 0 ≤ r ∧ r ≤ 1 ∧ L σ x * r = L (sw σ x y) x :=
        ⟨_, ratio_bounds (hL0 _ x) (step_x hsd hσ hxy)⟩
      have hpair := step_pair hsd hσ hxy hadj
      have hcol1 : ∀ b, ∑ a, L σ a * stepK r x y a b = L (sw σ x y) b := by
        intro b
        by_cases hbx : b = x
        · rw [hbx, stepK_col_x hne]; exact hrm
        · by_cases hby : b = y
          · rw [hby, stepK_col_y hne]
            linear_combination -hrm - hpair
          · rw [stepK_col_o (L σ) r hbx hby]
            exact (step_other hsd hσ hxy hadj hbx hby).symm
      refine ⟨kcomp (stepK r x y) K2, ?_, ?_, ?_, ?_⟩
      · intro a b
        exact sum_nonneg (fun c _ => mul_nonneg (stepK_nonneg hne hr0 hr1 a c) (h2n c b))
      · intro a
        unfold kcomp
        rw [sum_comm]
        simp_rw [← mul_sum, h2r, mul_one]
        exact stepK_row hne r a
      · intro b
        calc ∑ a, L σ a * kcomp (stepK r x y) K2 a b
            = ∑ c, (∑ a, L σ a * stepK r x y a c) * K2 c b := by
              unfold kcomp
              simp_rw [mul_sum, sum_mul, mul_assoc]
              rw [sum_comm]
          _ = ∑ c, L (sw σ x y) c * K2 c b := by simp_rw [hcol1]
          _ = L τ b := h2c b
      · intro a b hK
        unfold kcomp at hK
        obtain ⟨c, -, hc⟩ := exists_ne_zero_of_sum_ne_zero hK
        have h1 := stepK_supp r a c (left_ne_zero_of_mul hc)
        have h2 := h2s c b (right_ne_zero_of_mul hc)
        rcases h1 with hac | ⟨hax, hcy⟩
        · rw [← hac] at h2
          refine ⟨?_, h2.2⟩
          by_cases hab : a = b
          · rw [hab]
          · have e1 : sw σ x y a ≠ sw σ x y b := fun e => hab (hσ' e)
            have e2 : τ a ≠ τ b := fun e => hab (hτ e)
            exact (inv_sub hσ hxy hadj hyx (lt_of_le_of_ne h2.1 e1)
              (lt_of_le_of_ne h2.2 (Ne.symm e2))).le
        · rw [hax]
          rw [hcy] at h2
          have hτb : τ b < τ x := lt_of_le_of_lt h2.2 hyx
          refine ⟨?_, hτb.le⟩
          by_cases hyb : y = b
          · rw [← hyb]; exact hxy.le
          · have e1 : sw σ x y y ≠ sw σ x y b := fun e => hyb (hσ' e)
            have e2 : τ y ≠ τ b := fun e => hyb (hτ e)
            have := inv_sub hσ hxy hadj hyx (lt_of_le_of_ne h2.1 e1)
              (lt_of_le_of_ne h2.2 (Ne.symm e2))
            omega

/-- Hard direction: an SD-strategy-proof scheme admits a joint draw for every pair of ballots. -/
theorem joint_of_sd {L : (α → ℕ) → α → ℝ} (hL0 : ∀ σ a, 0 ≤ L σ a) (hsd : SDSP L)
    {σ τ : α → ℕ} (hσ : Function.Injective σ) (hτ : Function.Injective τ) :
    JointDraw σ τ (L σ) (L τ) := by
  obtain ⟨K, hn, hr, hc, hs⟩ := kernel_exists hL0 hsd _ σ τ rfl hσ hτ
  refine ⟨fun a b => L σ a * K a b, ?_, ?_, ?_, ?_⟩
  · intro a b; exact mul_nonneg (hL0 σ a) (hn a b)
  · intro a
    show ∑ b, L σ a * K a b = L σ a
    rw [← mul_sum, hr a, mul_one]
  · intro b; exact hc b
  · intro a b h; exact hs a b (right_ne_zero_of_mul h)

/-- Proposition 1 (one voter's slice): SD-strategy-proofness is equivalent to the existence of
joint draws on admissible pairs for every two ballots. -/
theorem prop1 {L : (α → ℕ) → α → ℝ} (hL0 : ∀ σ a, 0 ≤ L σ a) :
    SDSP L ↔ ∀ σ τ : α → ℕ, Function.Injective σ → Function.Injective τ →
      JointDraw σ τ (L σ) (L τ) := by
  constructor
  · intro hsd σ τ hσ hτ
    exact joint_of_sd hL0 hsd hσ hτ
  · intro h σ τ hσ hτ U hU
    exact sd_of_joint hσ (h σ τ hσ hτ) U hU

end JointDraws
