/-
  Proposition 7 of *Walls and Strategy* (working note *A tight form without
  a rational diagonal*, Section 6): in approval with a veto and a lottery on
  ties, approving exactly the proposals one prefers to the fallback is a
  strict Nash strategy, for any number n ≥ 2 of players. So no player has a
  rational diagonal.

  The procedure. Proposals form a finite type `P`, players a finite type `I`.
  Each player approves a set of proposals; the empty set is a veto. If the
  sets meet in K (`meet`), the outcome is the lottery `lam K`, which gives
  every member of K positive probability (`Lottery`); otherwise the fallback.
  Player k has expected utility `U k x` for proposal x and `f k` for the
  fallback, which may itself be a lottery (`value`, `payoff`).

  Strict Nash strategy with n players (`StrictNashN`): a strategy b of i that
  is a best reply to every profile of the others that is an equilibrium among
  them given b. A rational diagonal for i asks, for every b, for such a
  profile against which b is not a best reply, so a strict Nash strategy rules
  it out.

  * `sincere_strictNash`: the sincere set {x | U i x > f i} is a strict Nash
    strategy. The proof is the note's: at an equilibrium among the others the
    common set meets the sincere set in at most one proposal, since otherwise
    another player gains by approving only its favourite of them; against one
    common proposal y, every deviation gives the fallback or a lottery over
    proposals worth at most y; against none, every deviation gives the
    fallback or a lottery over proposals worth at most the fallback.

  The hypotheses are weaker than the note's genericity: only the other
  players' utilities need to be injective on the proposals, and the fallback
  may tie with a proposal. Not formalised: the computed comparisons of the
  note (deterministic ties, the coin as a fourth outcome, a fallback that
  reads declared ideals).
-/

module

public import Mathlib

@[expose] public section

open Finset

namespace ApprovalVeto

/-- A strict Nash strategy of player i with n players: a best reply to every
    profile of the others that is an equilibrium among them, given b. -/
def StrictNashN {I S : Type} [DecidableEq I] (pay : I → (I → S) → ℝ) (i : I) (b : S) : Prop :=
  ∀ σ : I → S, σ i = b →
    (∀ k, k ≠ i → ∀ t, pay k (Function.update σ k t) ≤ pay k σ) →
      ∀ t, pay i (Function.update σ i t) ≤ pay i σ

variable {I P : Type} [Fintype I] [DecidableEq I] [Fintype P] [DecidableEq P]

/-- Lotteries on ties: positive weight on every member of K, total weight 1. -/
structure Lottery (lam : Finset P → P → ℝ) : Prop where
  pos : ∀ K x, x ∈ K → 0 < lam K x
  sum : ∀ K : Finset P, K.Nonempty → ∑ x ∈ K, lam K x = 1

omit [DecidableEq I] in
/-- The proposals approved by every player. -/
def meet (σ : I → Finset P) : Finset P := univ.filter fun x => ∀ k, x ∈ σ k

/-- Expected utility of the outcome when the sets meet in K. -/
noncomputable def value (U : P → ℝ) (f : ℝ) (lam : Finset P → P → ℝ) (K : Finset P) : ℝ :=
  if K.Nonempty then ∑ x ∈ K, lam K x * U x else f

/-- Player k's expected utility at the profile σ. -/
noncomputable def payoff (U : I → P → ℝ) (f : I → ℝ) (lam : Finset P → P → ℝ) (k : I)
    (σ : I → Finset P) : ℝ :=
  value (U k) (f k) lam (meet σ)

omit [Fintype I] [DecidableEq I] in
/-- The sincere set: the proposals worth more than the fallback. -/
noncomputable def sincere (U : I → P → ℝ) (f : I → ℝ) (i : I) : Finset P :=
  univ.filter fun x => f i < U i x

omit [DecidableEq I] in
lemma mem_meet {σ : I → Finset P} {x : P} : x ∈ meet σ ↔ ∀ k, x ∈ σ k := by
  simp [meet]

lemma mem_meet_update {σ : I → Finset P} {k : I} {B : Finset P} {x : P} :
    x ∈ meet (Function.update σ k B) ↔ x ∈ B ∧ ∀ j, j ≠ k → x ∈ σ j := by
  rw [mem_meet]
  constructor
  · intro h
    refine ⟨by simpa using h k, fun j hj => ?_⟩
    have := h j
    rwa [Function.update_of_ne hj] at this
  · rintro ⟨hB, h⟩ j
    by_cases hj : j = k
    · subst hj
      simpa using hB
    · rw [Function.update_of_ne hj]
      exact h j hj

omit [Fintype I] [DecidableEq I] [DecidableEq P] in
lemma mem_sincere {U : I → P → ℝ} {f : I → ℝ} {i : I} {x : P} :
    x ∈ sincere U f i ↔ f i < U i x := by
  simp [sincere]

/-! ### Expected values of lotteries -/

omit [Fintype P] [DecidableEq P] in
/-- A lottery over proposals worth at most m is worth at most m. -/
lemma sum_le_of_le {lam : Finset P → P → ℝ} (hlam : Lottery lam) {K : Finset P}
    (hK : K.Nonempty) {U : P → ℝ} {m : ℝ} (h : ∀ x ∈ K, U x ≤ m) :
    ∑ x ∈ K, lam K x * U x ≤ m := by
  calc ∑ x ∈ K, lam K x * U x ≤ ∑ x ∈ K, lam K x * m :=
        sum_le_sum fun x hx => mul_le_mul_of_nonneg_left (h x hx) (hlam.pos K x hx).le
    _ = m := by rw [← sum_mul, hlam.sum K hK, one_mul]

omit [Fintype P] [DecidableEq P] in
/-- A lottery with full support over K, where z is the best member and some
    member is strictly worse, is worth strictly less than z. -/
lemma sum_lt_top {lam : Finset P → P → ℝ} (hlam : Lottery lam) {K : Finset P} {U : P → ℝ}
    {z w : P} (hz : z ∈ K) (hw : w ∈ K) (hwz : U w < U z) (h : ∀ x ∈ K, U x ≤ U z) :
    ∑ x ∈ K, lam K x * U x < U z := by
  have hK : K.Nonempty := ⟨z, hz⟩
  have hpos : 0 < ∑ x ∈ K, lam K x * (U z - U x) :=
    sum_pos' (fun x hx => mul_nonneg (hlam.pos K x hx).le (by linarith [h x hx]))
      ⟨w, hw, mul_pos (hlam.pos K w hw) (by linarith)⟩
  have e : ∑ x ∈ K, lam K x * (U z - U x) = U z - ∑ x ∈ K, lam K x * U x := by
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hlam.sum K hK, one_mul]
  linarith

omit [Fintype P] [DecidableEq P] in
lemma value_single {lam : Finset P → P → ℝ} (hlam : Lottery lam) (U : P → ℝ) (f : ℝ) (z : P) :
    value U f lam {z} = U z := by
  have h1 := hlam.sum {z} (singleton_nonempty z)
  rw [sum_singleton] at h1
  simp [value, h1]

omit [Fintype P] [DecidableEq P] in
lemma value_of_nonempty {lam : Finset P → P → ℝ} (U : P → ℝ) (f : ℝ) {K : Finset P}
    (hK : K.Nonempty) : value U f lam K = ∑ x ∈ K, lam K x * U x := by
  simp only [value, hK, ↓reduceIte]

omit [Fintype P] [DecidableEq P] in
lemma value_of_empty {lam : Finset P → P → ℝ} (U : P → ℝ) (f : ℝ) {K : Finset P}
    (hK : ¬ K.Nonempty) : value U f lam K = f := by
  simp only [value, hK, ↓reduceIte]

/-! ### Proposition 7 -/

/-- **Proposition 7.** In approval with a veto and a lottery on ties, the
    sincere set is a strict Nash strategy of every player, as long as there
    is another player and the others' utilities are injective on proposals. -/
theorem sincere_strictNash {U : I → P → ℝ} {f : I → ℝ} {lam : Finset P → P → ℝ}
    (hlam : Lottery lam) (i : I) (hU : ∀ k, k ≠ i → Function.Injective (U k))
    (hk : ∃ k, k ≠ i) : StrictNashN (payoff U f lam) i (sincere U f i) := by
  intro σ hσ heq B
  -- the common set meets the sincere set in at most one proposal
  have hM : ∀ y ∈ meet σ, ∀ w ∈ meet σ, y = w := by
    intro y hy w hw
    by_contra hyw
    obtain ⟨k, hki⟩ := hk
    obtain ⟨z, hzM, hzmax⟩ := (meet σ).exists_max_image (U k) ⟨y, hy⟩
    -- player k approving only z gets z
    have hmz : meet (Function.update σ k {z}) = {z} := by
      ext x
      rw [mem_meet_update, mem_singleton]
      constructor
      · exact fun h => h.1
      · rintro rfl
        exact ⟨rfl, fun j _ => mem_meet.mp hzM j⟩
    have hother : ∃ w' ∈ meet σ, w' ≠ z := by
      by_cases hyz : y = z
      · exact ⟨w, hw, fun e => hyw (hyz.trans e.symm)⟩
      · exact ⟨y, hy, hyz⟩
    obtain ⟨w', hw'M, hw'z⟩ := hother
    have hlt : U k w' < U k z :=
      lt_of_le_of_ne (hzmax w' hw'M) (fun e => hw'z (hU k hki e))
    have hdev := heq k hki {z}
    unfold payoff at hdev
    rw [hmz, value_single hlam, value_of_nonempty (K := meet σ) _ _ ⟨z, hzM⟩] at hdev
    have := sum_lt_top hlam hzM hw'M hlt hzmax
    linarith
  -- what i can reach lies in the others' common set
  have hK : ∀ x ∈ meet (Function.update σ i B), x ∈ sincere U f i → x ∈ meet σ := by
    intro x hx hA
    refine mem_meet.mpr fun j => ?_
    by_cases hj : j = i
    · subst hj
      rw [hσ]
      exact hA
    · exact (mem_meet_update.mp hx).2 j hj
  show value (U i) (f i) lam (meet (Function.update σ i B)) ≤ value (U i) (f i) lam (meet σ)
  by_cases hMne : (meet σ).Nonempty
  · -- one common proposal y, which i prefers to the fallback
    obtain ⟨y, hy⟩ := hMne
    have hMy : meet σ = {y} := eq_singleton_iff_unique_mem.mpr ⟨hy, fun x hx => hM x hx y hy⟩
    have hyA : f i < U i y := by
      have := mem_meet.mp hy i
      rw [hσ] at this
      exact mem_sincere.mp this
    rw [hMy, value_single hlam]
    by_cases hne : (meet (Function.update σ i B)).Nonempty
    · rw [value_of_nonempty _ _ hne]
      refine sum_le_of_le hlam hne fun x hx => ?_
      by_cases hA : f i < U i x
      · rw [hM x (hK x hx (mem_sincere.mpr hA)) y hy]
      · push Not at hA
        linarith
    · rw [value_of_empty _ _ hne]
      exact hyA.le
  · -- no common proposal: i gets the fallback, and cannot do better
    rw [value_of_empty _ _ hMne]
    by_cases hne : (meet (Function.update σ i B)).Nonempty
    · rw [value_of_nonempty _ _ hne]
      refine sum_le_of_le hlam hne fun x hx => ?_
      by_contra hlt
      push Not at hlt
      exact hMne ⟨x, hK x hx (mem_sincere.mpr hlt)⟩
    · rw [value_of_empty _ _ hne]

end ApprovalVeto
