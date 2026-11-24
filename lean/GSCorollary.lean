module

public import Mathlib
public import GSScenario
public import GSTopTwo

@[expose] public section

/-!
# Mixtures of dictatorships in the Gibbard–Satterthwaite scenario

*Gibbard–Satterthwaite as a Scenario*, Corollary 2 and the remark on anonymity, with
Gibbard's (1977) characterisation as an explicit hypothesis (`Gibbard1977`), as `Lotteries.lean`
does with Gibbard's 1978 corollary.

* `Gibbard1977`: every SD-strategy-proof random rule is a finite mixture of random rules
  (`GibbardMixture`), each *unilateral* (it depends on one voter's ballot only) or *duple* (it
  puts all probability on two fixed alternatives). Gibbard's theorem also makes the components
  strategy-proof, which is not needed here. A finite number of components is assumed; the
  theorem is stated with finite mixtures for finitely many voters and alternatives.
* `cor2`: a unanimous rule that is such a mixture, with at least three alternatives, is a
  mixture of dictatorships: weights `lam k` with `L π x = ∑ k, [x is k's top] · lam k`.
  Every component of positive weight is unanimous; a duple one fails at a unanimous profile
  whose top is outside its pair; a unilateral one gives what it gives at the unanimous profile
  built from its voter's ballot, that is, that voter's top.
* `cor2_models`: the families of one-profile marginals of empirical models that are unanimous
  are exactly the mixtures of dictatorships (one direction through `Gibbard1977`).
* `anonymous_uniform`: an anonymous mixture of dictatorships gives every voter the same weight:
  random dictatorship is the only anonymous one.
-/

open Finset Scenarios GSScenario

namespace GSCorollary

variable {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α]

/-! ### Tops of rankings -/

/-- `x` is the top of `ρ`. -/
def IsTop (ρ : PathPinning.Rk α) (x : α) : Prop := ∀ y, y ≠ x → ρ.1 x y = true

instance (ρ : PathPinning.Rk α) (x : α) : Decidable (IsTop ρ x) := by
  unfold IsTop; infer_instance

lemma isTop_unique {ρ : PathPinning.Rk α} {x y : α} (hx : IsTop ρ x) (hy : IsTop ρ y) :
    x = y := by
  by_contra hxy
  have h1 := hx y (Ne.symm hxy)
  have h2 := hy x hxy
  rw [PathPinning.asymm ρ h1] at h2
  exact Bool.false_ne_true h2

lemma exists_top [Nonempty α] (ρ : PathPinning.Rk α) : ∃ x, IsTop ρ x := by
  obtain ⟨x, hx⟩ := GSTopTwo.pos_surj ρ (k := 0) Fintype.card_pos
  refine ⟨x, fun y hy => (Rankings.pos_lt_iff ρ x y).mp ?_⟩
  have : Rankings.pos ρ y ≠ 0 := fun h => hy (Rankings.pos_inj ρ (h.trans hx.symm))
  omega

/-- The top of a ranking. -/
noncomputable def topOf [Nonempty α] (ρ : PathPinning.Rk α) : α :=
  Classical.choose (exists_top ρ)

lemma topOf_spec [Nonempty α] (ρ : PathPinning.Rk α) : IsTop ρ (topOf ρ) :=
  Classical.choose_spec (exists_top ρ)

/-- The ballot with `c` first. -/
lemma isTop_ballot (c : α) : IsTop (GSTopTwo.ballot c c) c := by
  intro y hy
  unfold GSTopTwo.ballot
  rw [Rankings.toRk_apply]
  simp [GSTopTwo.hmap, hy]

lemma sum_top {ρ : PathPinning.Rk α} {t : α} (ht : IsTop ρ t) (U : Finset α) (c : ℝ) :
    ∑ x ∈ U, (if IsTop ρ x then c else 0) = if t ∈ U then c else 0 := by
  have e : ∀ x, IsTop ρ x ↔ x = t := fun x =>
    ⟨fun hx => isTop_unique hx ht, fun h => by rw [h]; exact ht⟩
  simp_rw [e]
  simp

/-! ### Definitions -/

/-- Unanimity: if every voter ranks `a` first, `a` is chosen with certainty. -/
def Unanimous (L : Prof ι α → α → ℝ) : Prop :=
  ∀ π a, (∀ k, IsTop (π k) a) → L π a = 1

/-- The rule depends on one voter's ballot only. -/
def Unilateral (K : Prof ι α → α → ℝ) : Prop :=
  ∃ i, ∀ π π' : Prof ι α, π i = π' i → K π = K π'

/-- The rule puts all probability on two fixed alternatives. -/
def Duple (K : Prof ι α → α → ℝ) : Prop :=
  ∃ a b : α, ∀ (π : Prof ι α) x, x ≠ a → x ≠ b → K π x = 0

/-- A finite mixture of random rules, each unilateral or duple. -/
def GibbardMixture (L : Prof ι α → α → ℝ) : Prop :=
  ∃ (n : ℕ) (w : Fin n → ℝ) (K : Fin n → Prof ι α → α → ℝ),
    (∀ j, 0 ≤ w j) ∧ ∑ j, w j = 1 ∧ (∀ j π x, 0 ≤ K j π x) ∧ (∀ j π, ∑ x, K j π x = 1) ∧
    (∀ j, Unilateral (K j) ∨ Duple (K j)) ∧ ∀ π x, L π x = ∑ j, w j * K j π x

variable (ι α) in
/-- Gibbard (1977), as a hypothesis: SD-strategy-proof random rules are such mixtures. -/
def Gibbard1977 : Prop :=
  ∀ L : Prof ι α → α → ℝ, (∀ π x, 0 ≤ L π x) → (∀ π, ∑ x, L π x = 1) → SDSPRule L →
    GibbardMixture L

/-- The mixture of dictatorships with weights `lam`. -/
def LD (lam : ι → ℝ) (π : Prof ι α) (x : α) : ℝ := ∑ k, if IsTop (π k) x then lam k else 0

/-- A mixture of dictatorships. -/
def IsMixtureDict (L : Prof ι α → α → ℝ) : Prop :=
  ∃ lam : ι → ℝ, (∀ k, 0 ≤ lam k) ∧ ∑ k, lam k = 1 ∧ ∀ π x, L π x = LD lam π x

/-! ### Corollary 2 -/

omit [Fintype ι] [DecidableEq ι] [Fintype α] [DecidableEq α] in
lemma comp_one {n : ℕ} {w k : Fin n → ℝ} (hw0 : ∀ j, 0 ≤ w j) (hw1 : ∑ j, w j = 1)
    (hk1 : ∀ j, k j ≤ 1) (hs : ∑ j, w j * k j = 1) (j : Fin n) (hj : w j ≠ 0) : k j = 1 := by
  have hz : ∑ j, w j * (1 - k j) = 0 := by
    simp_rw [mul_sub, mul_one, sum_sub_distrib, hw1, hs, sub_self]
  have hnn : ∀ j ∈ (univ : Finset (Fin n)), 0 ≤ w j * (1 - k j) :=
    fun j _ => mul_nonneg (hw0 j) (by linarith [hk1 j])
  have h := (sum_eq_zero_iff_of_nonneg hnn).mp hz j (mem_univ j)
  rcases mul_eq_zero.mp h with h' | h'
  · exact absurd h' hj
  · linarith

/-- Corollary 2: with unanimity and at least three alternatives, a mixture of unilateral and
duple rules is a mixture of dictatorships. -/
theorem cor2 [Nonempty ι] (h3 : 3 ≤ Fintype.card α) {L : Prof ι α → α → ℝ}
    (hmix : GibbardMixture L) (hun : Unanimous L) : IsMixtureDict L := by
  classical
  obtain ⟨n, w, K, hw0, hw1, hK0, hK1, hcomp, hL⟩ := hmix
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  have hKle : ∀ j π x, K j π x ≤ 1 := fun j π x => by
    rw [← hK1 j π]
    exact single_le_sum (f := K j π) (fun y _ => hK0 j π y) (mem_univ x)
  -- every component of positive weight is unanimous
  have hcu : ∀ j, w j ≠ 0 → ∀ (π : Prof ι α) a, (∀ k, IsTop (π k) a) → K j π a = 1 := by
    intro j hj π a ha
    have h1 := hun π a ha
    rw [hL] at h1
    exact comp_one hw0 hw1 (fun j => hKle j π a) h1 j hj
  -- no component of positive weight is duple
  have hnd : ∀ j, w j ≠ 0 → ¬ Duple (K j) := by
    rintro j hj ⟨a, b, hab⟩
    obtain ⟨c, hca, hcb⟩ : ∃ c, c ≠ a ∧ c ≠ b := by
      by_contra hno
      push Not at hno
      have hsub : (univ : Finset α) ⊆ {a, b} := by
        intro c _
        by_cases hca : c = a
        · rw [hca]; exact mem_insert_self a {b}
        · rw [hno c hca]; exact mem_insert_of_mem (mem_singleton_self b)
      have hc := card_le_card hsub
      rw [card_univ] at hc
      have := card_insert_le a ({b} : Finset α)
      rw [card_singleton] at this
      omega
    have h1 := hcu j hj (fun _ => GSTopTwo.ballot c c) c (fun _ => isTop_ballot c)
    rw [hab _ c hca hcb] at h1
    exact zero_ne_one h1
  -- the voter of each component of positive weight
  have hvoter : ∀ j, ∃ i : ι, w j ≠ 0 → ∀ π π' : Prof ι α, π i = π' i → K j π = K j π' := by
    intro j
    by_cases hj : w j = 0
    · exact ⟨Classical.arbitrary ι, fun h => absurd hj h⟩
    · rcases hcomp j with ⟨i, hi⟩ | hd
      · exact ⟨i, fun _ => hi⟩
      · exact absurd hd (hnd j hj)
  choose v hv using hvoter
  -- a component of positive weight is the dictatorship of its voter
  have hdict : ∀ j, w j ≠ 0 → ∀ (π : Prof ι α) x,
      K j π x = if IsTop (π (v j)) x then 1 else 0 := by
    intro j hj π x
    obtain ⟨t, ht⟩ := exists_top (π (v j))
    have hπ' : K j π = K j (fun _ => π (v j)) := hv j hj π _ rfl
    have h1 : K j π t = 1 := by
      rw [hπ']
      exact hcu j hj _ t (fun _ => ht)
    by_cases hx : IsTop (π (v j)) x
    · rw [ite_eq_left hx, isTop_unique hx ht]
      exact h1
    · rw [ite_eq_right hx]
      have hxt : x ≠ t := fun e => hx (by rw [e]; exact ht)
      have hs := hK1 j π
      rw [← add_sum_erase univ (K j π) (mem_univ t), h1] at hs
      have h0 : ∑ y ∈ univ.erase t, K j π y = 0 := by linarith
      exact (sum_eq_zero_iff_of_nonneg (fun y _ => hK0 j π y)).mp h0 x
        (mem_erase.mpr ⟨hxt, mem_univ x⟩)
  refine ⟨fun k => ∑ j, if v j = k then w j else 0, ?_, ?_, ?_⟩
  · intro k
    exact sum_nonneg (fun j _ => by split_ifs <;> simp [hw0 j])
  · rw [sum_comm]
    simp [hw1]
  · intro π x
    rw [hL]
    have hterm : ∀ j, w j * K j π x = if IsTop (π (v j)) x then w j else 0 := by
      intro j
      by_cases hj : w j = 0
      · simp [hj]
      · rw [hdict j hj π x]
        split_ifs <;> simp
    simp_rw [hterm]
    unfold LD
    symm
    calc ∑ k, (if IsTop (π k) x then ∑ j, (if v j = k then w j else 0) else 0)
        = ∑ k, ∑ j, (if IsTop (π k) x then (if v j = k then w j else 0) else 0) := by
          refine sum_congr rfl (fun k _ => ?_)
          split_ifs <;> simp
      _ = ∑ j, ∑ k, (if IsTop (π k) x then (if v j = k then w j else 0) else 0) := sum_comm
      _ = ∑ j, (if IsTop (π (v j)) x then w j else 0) := by
          refine sum_congr rfl (fun j _ => ?_)
          have h0 : ∀ k, k ≠ v j →
              (if IsTop (π k) x then (if v j = k then w j else 0) else 0) = 0 :=
            fun k hk => by simp [Ne.symm hk]
          rw [Fintype.sum_eq_single (v j) h0]
          simp

/-! ### Mixtures of dictatorships are unanimous empirical models -/

omit [DecidableEq ι] in
lemma probU [Nonempty α] (lam : ι → ℝ) (π : Prof ι α) (U : Finset α) :
    ∑ x ∈ U, LD lam π x = ∑ k, (if topOf (π k) ∈ U then lam k else 0) := by
  unfold LD
  rw [sum_comm]
  exact sum_congr rfl (fun k _ => sum_top (topOf_spec (π k)) U (lam k))

lemma sdsp_LD [Nonempty α] {lam : ι → ℝ} (h0 : ∀ k, 0 ≤ lam k) : SDSPRule (LD (α := α) lam) := by
  intro π k ρ τ U hU
  show ∑ a ∈ U, LD lam (Function.update π k τ) a ≤ ∑ a ∈ U, LD lam (Function.update π k ρ) a
  rw [probU, probU]
  apply sum_le_sum
  intro k' _
  by_cases hk : k' = k
  · simp only [hk, Function.update_self]
    by_cases hτ : topOf τ ∈ U
    · have hρ : topOf ρ ∈ U := by
        by_cases e : topOf ρ = topOf τ
        · rw [e]; exact hτ
        · exact hU _ _ hτ (topOf_spec ρ _ (Ne.symm e))
      rw [ite_eq_left hτ, ite_eq_left hρ]
    · rw [ite_eq_right hτ]
      split_ifs <;> simp [h0 k]
  · simp [hk]

omit [DecidableEq ι] in
lemma LD_nonneg {lam : ι → ℝ} (h0 : ∀ k, 0 ≤ lam k) (π : Prof ι α) (x : α) : 0 ≤ LD lam π x :=
  sum_nonneg (fun k _ => by split_ifs <;> simp [h0 k])

lemma LD_sum [Nonempty α] {lam : ι → ℝ} (h1 : ∑ k, lam k = 1) (π : Prof ι α) :
    ∑ x, LD lam π x = 1 := by
  rw [probU]
  simp [h1]

omit [DecidableEq ι] in
lemma LD_unanimous {lam : ι → ℝ} (h1 : ∑ k, lam k = 1) : Unanimous (LD (α := α) lam) := by
  intro π a ha
  unfold LD
  simp [ha, h1]

/-- The families of one-profile marginals of empirical models that are unanimous are exactly
the mixtures of dictatorships, given Gibbard's characterisation. -/
theorem cor2_models [Nonempty ι] (hG : Gibbard1977 ι α) (h3 : 3 ≤ Fintype.card α)
    {L : Prof ι α → α → ℝ} (hL0 : ∀ π x, 0 ≤ L π x) (hL1 : ∀ π, ∑ x, L π x = 1) :
    ((∃ e, Model (GS : Scenario (Prof ι α) α) e ∧ HasMarginals e L) ∧ Unanimous L) ↔
      IsMixtureDict L := by
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  constructor
  · rintro ⟨hm, hun⟩
    exact cor2 h3 (hG L hL0 hL1 ((gs_prop1 hL0 hL1).mp hm)) hun
  · rintro ⟨lam, h0, h1, hL⟩
    have e : L = LD lam := funext (fun π => funext (fun x => hL π x))
    subst e
    exact ⟨(gs_prop1 hL0 hL1).mpr (sdsp_LD h0), LD_unanimous h1⟩

/-! ### Anonymity -/

/-- Anonymity: permuting the voters does not change the lottery. -/
def Anonymous (L : Prof ι α → α → ℝ) : Prop :=
  ∀ (s : Equiv.Perm ι) (π : Prof ι α), L (fun k => π (s k)) = L π

/-- An anonymous mixture of dictatorships is random dictatorship. -/
theorem anonymous_uniform (h2 : 2 ≤ Fintype.card α) {lam : ι → ℝ} (h1 : ∑ k, lam k = 1)
    (hanon : Anonymous (LD (α := α) lam)) (k : ι) : lam k = 1 / Fintype.card ι := by
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  -- voter `k₀` ranks `a` first, the others `b`
  let P : ι → Prof ι α := fun k₀ k' => if k' = k₀ then GSTopTwo.ballot a a else GSTopTwo.ballot b b
  have hval : ∀ k₀, LD lam (P k₀) a = lam k₀ := by
    intro k₀
    unfold LD
    have h0 : ∀ k', k' ≠ k₀ → (if IsTop (P k₀ k') a then lam k' else 0) = 0 := by
      intro k' hk'
      apply ite_eq_right
      intro htop
      have hb : P k₀ k' = GSTopTwo.ballot b b := by simp [P, hk']
      rw [hb] at htop
      exact hab (isTop_unique htop (isTop_ballot b))
    rw [Fintype.sum_eq_single k₀ h0]
    have ha : P k₀ k₀ = GSTopTwo.ballot a a := by simp [P]
    rw [ha, ite_eq_left (isTop_ballot a)]
  have hconst : ∀ k₁ k₂, lam k₁ = lam k₂ := by
    intro k₁ k₂
    have hP : (fun k' => P k₁ (Equiv.swap k₁ k₂ k')) = P k₂ := by
      funext k'
      have e : (Equiv.swap k₁ k₂ k' = k₁) ↔ k' = k₂ := by
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
      simp only [P, e]
    have := congrFun (hanon (Equiv.swap k₁ k₂) (P k₁)) a
    rw [hP, hval, hval] at this
    exact this.symm
  have hsum : ∑ k', lam k' = Fintype.card ι * lam k := by
    rw [sum_congr rfl (fun k' _ => hconst k' k)]
    simp
  have hcard : (0 : ℝ) < Fintype.card ι := by
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨k⟩
    exact_mod_cast this
  rw [h1] at hsum
  rw [eq_div_iff hcard.ne', mul_comm]
  exact hsum.symm

end GSCorollary
