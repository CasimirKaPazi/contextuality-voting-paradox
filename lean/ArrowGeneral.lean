module

public import Mathlib
public import PathPinning

@[expose] public section

/-!
# Theorem 5′: empirical models of Arrow's scenario are mixtures of dictatorships

General framework and induction (*Theorem 5 for any number of alternatives*, working note).

* Rankings of a finite type `α` are `PathPinning.Rk α` (strict total orders as Boolean relations).
* A profile assigns a ranking to every voter `k : ι`.
* A model `μ π σ` gives, at every profile `π`, a probability law on social rankings `σ`.
  *Full compatibility*: the probability of an event determined by the comparisons on a set `S` of
  ordered pairs depends only on the voters' comparisons on `S`. *Unanimity*: if every voter ranks
  `x` above `y`, the social ranking does so with probability 1.
* A *mixture of dictatorships*: weights `w k ≥ 0` summing to 1 with
  `μ π σ = ∑ (k with π k = σ) w k`.

`mixture_of_base`: if every model on three alternatives is a mixture, so is every model on any
number `≥ 3` of alternatives. The three-alternative case is `ProbabilisticArrow.lean`; the bridge
between the two encodings is in `ArrowBase.lean`.
-/

open Finset PathPinning

namespace ArrowGeneral

universe u v

section Defs
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {α : Type u} [Fintype α] [DecidableEq α]

/-- The Boolean event `E` is determined by the comparisons on `S`. -/
def Det (S : Finset (α × α)) (E : Rk α → Bool) : Prop :=
  ∀ σ σ' : Rk α, (∀ p ∈ S, σ.1 p.1 p.2 = σ'.1 p.1 p.2) → E σ = E σ'

/-- Two profiles agree on the comparisons in `S`, voter by voter. -/
def AgreeP (S : Finset (α × α)) (π π' : ι → Rk α) : Prop :=
  ∀ k, ∀ p ∈ S, (π k).1 p.1 p.2 = (π' k).1 p.1 p.2

/-- Probability of a Boolean event. -/
def prob (μ : (ι → Rk α) → Rk α → ℝ) (π : ι → Rk α) (E : Rk α → Bool) : ℝ :=
  ∑ σ ∈ univ.filter (fun σ => E σ = true), μ π σ

/-- Empirical model on Arrow's scenario: full compatibility and unanimity. -/
structure Model (μ : (ι → Rk α) → Rk α → ℝ) : Prop where
  nonneg : ∀ π σ, 0 ≤ μ π σ
  total : ∀ π, ∑ σ, μ π σ = 1
  compat : ∀ (S : Finset (α × α)) (E : Rk α → Bool), Det S E →
    ∀ π π', AgreeP S π π' → prob μ π E = prob μ π' E
  unan : ∀ π x y, (∀ k, (π k).1 x y = true) → prob μ π (fun σ => σ.1 x y) = 1

/-- Mixture of dictatorships. -/
def IsMixture (μ : (ι → Rk α) → Rk α → ℝ) : Prop :=
  ∃ w : ι → ℝ, (∀ k, 0 ≤ w k) ∧ ∑ k, w k = 1 ∧
    ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k

lemma det_mono {S S' : Finset (α × α)} {E : Rk α → Bool} (h : Det S E) (hS : S ⊆ S') :
    Det S' E := fun σ σ' hag => h σ σ' (fun p hp => hag p (hS hp))

omit [DecidableEq ι] in
/-- The probability of an event under a mixture. -/
lemma prob_mixture (μ : (ι → Rk α) → Rk α → ℝ) (w : ι → ℝ)
    (hmix : ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k)
    (π : ι → Rk α) (E : Rk α → Bool) :
    prob μ π E = ∑ k ∈ univ.filter (fun k => E (π k) = true), w k := by
  unfold prob
  simp_rw [hmix π]
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ.filter (fun k => E (π k) = true))
    (t := univ.filter (fun σ => E σ = true)) (g := π) (f := w)
    (fun k hk => by simpa using hk)]
  refine Finset.sum_congr rfl (fun σ hσ => ?_)
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  constructor
  · intro h; exact ⟨by rw [h]; exact hσ, h⟩
  · intro h; exact h.2

lemma filter_decide (p : Rk α → Prop) [DecidablePred p] :
    univ.filter (fun σ => decide (p σ) = true) = univ.filter p := by
  ext σ; simp

end Defs

/-! ## Basic rankings -/

section Rankings
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- The ranking given by a fixed enumeration of `α`. -/
noncomputable def baseRk : Rk α :=
  ⟨fun x y => decide (Fintype.equivFin α x < Fintype.equivFin α y), by
    unfold IsRank
    refine ⟨fun x => by simp, fun x y z h1 h2 => ?_, fun x y hxy => ?_⟩
    · simp only [decide_eq_true_eq] at h1 h2 ⊢; exact lt_trans h1 h2
    · simp only [decide_eq_true_eq]
      have : Fintype.equivFin α x ≠ Fintype.equivFin α y := fun e => hxy ((Fintype.equivFin α).injective e)
      exact lt_or_gt_of_ne this⟩

/-- The reverse of a ranking. -/
def revRk (σ : Rk α) : Rk α :=
  ⟨fun x y => σ.1 y x, by
    unfold IsRank
    refine ⟨fun x => σ.2.1 x, fun x y z h1 h2 => σ.2.2.1 z y x h2 h1, fun x y hxy => ?_⟩
    rcases σ.2.2.2 x y hxy with h | h
    · exact Or.inr h
    · exact Or.inl h⟩

/-- For distinct `a, b` there are rankings with `a` above `b` and with `b` above `a`. -/
lemma exists_rk_above {a b : α} (hab : a ≠ b) : ∃ σ : Rk α, σ.1 a b = true := by
  rcases PathPinning.total (baseRk (α := α)) hab with h | h
  · exact ⟨baseRk, h⟩
  · exact ⟨revRk baseRk, h⟩

/-- Every non-empty finite set has a top element in a ranking. -/
lemma exists_top (σ : Rk α) (S : Finset α) (hS : S.Nonempty) :
    ∃ x ∈ S, ∀ v ∈ S, v ≠ x → σ.1 x v = true := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image S
    (fun x => (S.filter (fun v => σ.1 x v = true)).card) hS
  refine ⟨x, hx, fun v hv hvx => ?_⟩
  by_contra hne
  have hvx' : σ.1 v x = true := by
    rcases PathPinning.total σ hvx with h | h
    · exact h
    · exact absurd h hne
  have hsub : S.filter (fun u => σ.1 x u = true) ⊂ S.filter (fun u => σ.1 v u = true) := by
    rw [Finset.ssubset_iff_of_subset]
    · refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter]; exact ⟨hx, hvx'⟩
      · simp only [Finset.mem_filter, not_and]; intro _; rw [PathPinning.irrefl]; simp
    · intro u hu
      simp only [Finset.mem_filter] at hu ⊢
      exact ⟨hu.1, PathPinning.trans' σ hvx' hu.2⟩
  have h1 := Finset.card_lt_card hsub
  have h2 : (S.filter (fun u => σ.1 v u = true)).card ≤ (S.filter (fun u => σ.1 x u = true)).card :=
    hmax v hv
  omega

/-- Move `x` to directly below `y`. -/
def moveBelow (ρ : Rk α) (x y : α) (hxy : x ≠ y) : Rk α :=
  ⟨fun u v => if u = x then (if v = x then false else (decide (v ≠ y) && ρ.1 y v))
    else (if v = x then (decide (u = y) || ρ.1 u y) else ρ.1 u v), by
    unfold IsRank
    refine ⟨fun u => ?_, fun u v w h1 h2 => ?_, fun u v huv => ?_⟩
    · by_cases hu : u = x <;> simp [hu, PathPinning.irrefl]
    · by_cases hu : u = x <;> by_cases hv : v = x <;> by_cases hw : w = x <;>
        simp only [hu, hv, hw, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          Bool.or_eq_true, ne_eq] at h1 h2 ⊢
      · exact absurd h1 (by simp)
      · exact absurd h1 (by simp)
      · -- u = x, v ≠ x, w = x: impossible
        rcases h2 with h | h
        · exact absurd h h1.1
        · rw [PathPinning.asymm ρ h1.2] at h; exact absurd h (by simp)
      · -- u = x, v ≠ x, w ≠ x
        refine ⟨fun hwy => ?_, PathPinning.trans' ρ h1.2 h2⟩
        subst hwy; rw [PathPinning.asymm ρ h1.2] at h2; exact absurd h2 (by simp)
      · exact absurd h2 (by simp)
      · -- u ≠ x, v = x, w ≠ x
        rcases h1 with h | h
        · subst h; exact h2.2
        · exact PathPinning.trans' ρ h h2.2
      · -- u ≠ x, v ≠ x, w = x
        rcases h2 with h | h
        · subst h; exact Or.inr h1
        · exact Or.inr (PathPinning.trans' ρ h1 h)
      · exact PathPinning.trans' ρ h1 h2
    · by_cases hu : u = x <;> by_cases hv : v = x
      · exact absurd (hu.trans hv.symm) huv
      · simp only [hu, hv, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          Bool.or_eq_true, ne_eq]
        by_cases hvy : v = y
        · exact Or.inr (Or.inl hvy)
        · rcases PathPinning.total ρ (Ne.symm hvy) with h | h
          · exact Or.inl ⟨hvy, h⟩
          · exact Or.inr (Or.inr h)
      · simp only [hu, hv, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
          Bool.or_eq_true, ne_eq]
        by_cases huy : u = y
        · exact Or.inl (Or.inl huy)
        · rcases PathPinning.total ρ (Ne.symm huy) with h | h
          · exact Or.inr ⟨huy, h⟩
          · exact Or.inl (Or.inr h)
      · simp only [hu, hv, ↓reduceIte]; exact PathPinning.total ρ huv⟩

lemma moveBelow_off (ρ : Rk α) {x y : α} (hxy : x ≠ y) {u v : α} (hu : u ≠ x) (hv : v ≠ x) :
    (moveBelow ρ x y hxy).1 u v = ρ.1 u v := by
  simp [moveBelow, hu, hv]

end Rankings

/-! ## Sub-models on fewer alternatives -/

section Restrict
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {α : Type u} [Fintype α] [DecidableEq α]
variable (A : Finset α)

/-- Restriction of a ranking to `A`. -/
def res (σ : Rk α) : Rk A :=
  ⟨fun x y => σ.1 x y, by
    unfold IsRank
    exact ⟨fun x => σ.2.1 x, fun x y z h1 h2 => σ.2.2.1 x y z h1 h2,
      fun x y h => σ.2.2.2 x y (fun e => h (Subtype.ext e))⟩⟩

/-- Extension of a ranking of `A`: `A` on top, the rest below in a fixed order. -/
noncomputable def extR (ρ : Rk A) : Rk α :=
  ⟨fun x y => if hx : x ∈ A then (if hy : y ∈ A then ρ.1 ⟨x, hx⟩ ⟨y, hy⟩ else true)
    else (if hy : y ∈ A then false
      else decide (Fintype.equivFin α x < Fintype.equivFin α y)), by
    unfold IsRank
    refine ⟨fun x => ?_, fun x y z h1 h2 => ?_, fun x y hxy => ?_⟩
    · by_cases hx : x ∈ A <;> simp [hx, PathPinning.irrefl]
    · by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> by_cases hz : z ∈ A <;>
        simp [hx, hy, hz] at h1 h2 ⊢ <;>
        first
        | exact PathPinning.trans' ρ h1 h2
        | exact lt_trans h1 h2
    · by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp [hx, hy] <;>
        first
        | exact PathPinning.total ρ (fun e => hxy (congrArg Subtype.val e))
        | exact hxy⟩

lemma extR_val (ρ : Rk A) {x y : α} (hx : x ∈ A) (hy : y ∈ A) :
    (extR A ρ).1 x y = ρ.1 ⟨x, hx⟩ ⟨y, hy⟩ := by
  simp [extR, hx, hy]

lemma res_extR (ρ : Rk A) : res A (extR A ρ) = ρ := by
  apply Subtype.ext; funext x y
  simp [res, extR]

lemma extR_res_val (σ : Rk α) {x y : α} (hx : x ∈ A) (hy : y ∈ A) :
    (extR A (res A σ)).1 x y = σ.1 x y := by
  rw [extR_val A _ hx hy]; rfl

/-- The sub-model on `A`, evaluated through the extension of profiles. -/
noncomputable def subModel (μ : (ι → Rk α) → Rk α → ℝ) : (ι → Rk A) → Rk A → ℝ :=
  fun πA ρ => ∑ σ ∈ univ.filter (fun σ => res A σ = ρ), μ (fun k => extR A (πA k)) σ

omit [Fintype ι] [DecidableEq ι] in
lemma prob_subModel (μ : (ι → Rk α) → Rk α → ℝ) (πA : ι → Rk A) (E : Rk A → Bool) :
    prob (subModel A μ) πA E = prob μ (fun k => extR A (πA k)) (fun σ => E (res A σ)) := by
  unfold prob subModel
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := univ.filter (fun σ => E (res A σ) = true))
    (t := univ.filter (fun ρ => E ρ = true)) (g := res A)
    (f := fun σ => μ (fun k => extR A (πA k)) σ) (fun σ hσ => by simpa using hσ)]
  refine Finset.sum_congr rfl (fun ρ hρ => ?_)
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext σ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hρ ⊢
  constructor
  · intro h; exact ⟨by rw [h]; exact hρ, h⟩
  · intro h; exact h.2

/-- The pairs inside `A`. -/
def pairsIn : Finset (α × α) := A ×ˢ A

omit [Fintype α] [DecidableEq α] in
lemma mem_pairsIn {p : α × α} : p ∈ pairsIn A ↔ p.1 ∈ A ∧ p.2 ∈ A := Finset.mem_product

omit [Fintype ι] [DecidableEq ι] in
/-- The sub-model is again a model. -/
theorem subModel_model {μ : (ι → Rk α) → Rk α → ℝ} (hM : Model μ) : Model (subModel A μ) where
  nonneg πA ρ := Finset.sum_nonneg (fun σ _ => hM.nonneg _ σ)
  total πA := by
    have := hM.total (fun k => extR A (πA k))
    rw [← this]
    unfold subModel
    exact Finset.sum_fiberwise univ (res A) _
  compat S E hE πA πA' hag := by
    rw [prob_subModel, prob_subModel]
    apply hM.compat (S.image (fun p => ((p.1 : α), (p.2 : α))))
    · intro σ σ' h
      apply hE
      intro p hp
      exact h _ (Finset.mem_image_of_mem _ hp)
    · intro k p hp
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp
      show (extR A (πA k)).1 (q.1 : α) (q.2 : α) = (extR A (πA' k)).1 (q.1 : α) (q.2 : α)
      rw [extR_val A _ q.1.2 q.2.2, extR_val A _ q.1.2 q.2.2]
      exact hag k q hq
  unan πA x y h := by
    rw [prob_subModel]
    have := hM.unan (fun k => extR A (πA k)) x y (fun k => by rw [extR_val A _ x.2 y.2]; exact h k)
    exact this

omit [DecidableEq ι] in
/-- If the sub-model on `A` is a mixture with weights `w`, events determined inside `A` have the
mixture's probability in the full model. -/
theorem prob_of_sub_mixture {μ : (ι → Rk α) → Rk α → ℝ} (hM : Model μ) (w : ι → ℝ)
    (hmix : ∀ πA σ, subModel A μ πA σ = ∑ k ∈ univ.filter (fun k => πA k = σ), w k)
    (π : ι → Rk α) (E : Rk α → Bool) (hE : Det (pairsIn A) E) :
    prob μ π E = ∑ k ∈ univ.filter (fun k => E (π k) = true), w k := by
  have hEres : ∀ σ, E σ = E (extR A (res A σ)) := fun σ =>
    hE σ _ (fun p hp => by
      rw [mem_pairsIn] at hp
      rw [extR_res_val A σ hp.1 hp.2])
  have h1 : prob μ π E = prob μ (fun k => extR A (res A (π k))) E := by
    apply hM.compat (pairsIn A) E hE
    intro k p hp
    rw [mem_pairsIn] at hp
    rw [extR_res_val A (π k) hp.1 hp.2]
  have h2 : prob μ (fun k => extR A (res A (π k))) E =
      prob (subModel A μ) (fun k => res A (π k)) (fun ρ => E (extR A ρ)) := by
    rw [prob_subModel]
    congr 1
    funext σ
    exact hEres σ
  rw [h1, h2, prob_mixture _ w hmix]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hEres]

end Restrict

/-! ## The completion of Step 3 -/

section Completion
variable {α : Type u} [Fintype α] [DecidableEq α]

/-- `a₂` is above both or below both of `a₁` and `a₃`. -/
def Pat (ρ : Rk α) (a₁ a₂ a₃ : α) : Prop :=
  (ρ.1 a₂ a₁ = true ∧ ρ.1 a₂ a₃ = true) ∨ (ρ.1 a₁ a₂ = true ∧ ρ.1 a₃ a₂ = true)

instance (ρ : Rk α) (a₁ a₂ a₃ : α) : Decidable (Pat ρ a₁ a₂ a₃) := by unfold Pat; infer_instance

/-- The completion: if `a₂` is above both or below both and `a₁` is above `a₃`, move `a₁` to
directly below `a₃`. -/
def complete (ρ : Rk α) (a₁ a₂ a₃ : α) (h31 : a₃ ≠ a₁) : Rk α :=
  if Pat ρ a₁ a₂ a₃ ∧ ρ.1 a₁ a₃ = true then moveBelow ρ a₁ a₃ (Ne.symm h31) else ρ

variable {a₁ a₂ a₃ : α}

lemma complete_off (ρ : Rk α) (h31 : a₃ ≠ a₁) {u v : α} (hu : u ≠ a₁) (hv : v ≠ a₁) :
    (complete ρ a₁ a₂ a₃ h31).1 u v = ρ.1 u v := by
  unfold complete; split_ifs
  · exact moveBelow_off ρ (Ne.symm h31) hu hv
  · rfl

lemma complete_12 (ρ : Rk α) (h21 : a₂ ≠ a₁) (h32 : a₃ ≠ a₂) (h31 : a₃ ≠ a₁) :
    (complete ρ a₁ a₂ a₃ h31).1 a₁ a₂ = ρ.1 a₁ a₂ ∧
      (complete ρ a₁ a₂ a₃ h31).1 a₂ a₁ = ρ.1 a₂ a₁ := by
  unfold complete; split_ifs with hcond
  · obtain ⟨hp, -⟩ := hcond
    rcases hp with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp [moveBelow, h21, Ne.symm h32, h1, h2, PathPinning.asymm ρ h1, PathPinning.asymm ρ h2]
    · simp [moveBelow, h21, Ne.symm h32, h1, h2, PathPinning.asymm ρ h1, PathPinning.asymm ρ h2]
  · exact ⟨rfl, rfl⟩

lemma complete_comp (ρ : Rk α) (h31 : a₃ ≠ a₁) :
    Pat (complete ρ a₁ a₂ a₃ h31) a₁ a₂ a₃ → (complete ρ a₁ a₂ a₃ h31).1 a₃ a₁ = true := by
  unfold complete; split_ifs with hcond
  · intro _; simp [moveBelow, h31]
  · intro hp
    have h13 : ρ.1 a₁ a₃ ≠ true := fun h => hcond ⟨hp, h⟩
    rcases PathPinning.total ρ (Ne.symm h31) with h | h
    · exact absurd h h13
    · exact h

lemma complete_eq (ρ t : Rk α) (h31 : a₃ ≠ a₁) (t12 : t.1 a₁ a₂ = true) (t23 : t.1 a₂ a₃ = true) :
    complete ρ a₁ a₂ a₃ h31 = t ↔ ρ = t := by
  have t13 : t.1 a₁ a₃ = true := PathPinning.trans' t t12 t23
  constructor
  · unfold complete; split_ifs with hcond
    · intro h
      exfalso
      have h31' : (moveBelow ρ a₁ a₃ (Ne.symm h31)).1 a₃ a₁ = true := by simp [moveBelow, h31]
      rw [h, PathPinning.asymm t t13] at h31'; exact absurd h31' (by simp)
    · exact id
  · intro h; subst h
    have hn : ¬(Pat ρ a₁ a₂ a₃ ∧ ρ.1 a₁ a₃ = true) := by
      rintro ⟨hp, -⟩
      rcases hp with ⟨h1, -⟩ | ⟨-, h2⟩
      · rw [PathPinning.asymm ρ t12] at h1; exact absurd h1 (by simp)
      · rw [PathPinning.asymm ρ t23] at h2; exact absurd h2 (by simp)
    unfold complete
    simp only [hn, ↓reduceIte]

end Completion

/-! ## The induction step -/

section Step
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {α : Type u} [Fintype α] [DecidableEq α]

lemma det_rel {a b : α} {S : Finset (α × α)} (h : (a, b) ∈ S) : Det S (fun σ => σ.1 a b) :=
  fun _ _ hag => hag (a, b) h

lemma det_agree (T : Finset α) (ρ : Rk α) :
    Det (pairsIn T) (fun σ => decide (Agree T σ ρ)) := by
  intro σ σ' hag
  have : Agree T σ ρ ↔ Agree T σ' ρ := by
    constructor
    · intro h x hx y hy; rw [← h x hx y hy]; exact (hag (x, y) ((mem_pairsIn T).mpr ⟨hx, hy⟩)).symm
    · intro h x hx y hy; rw [← h x hx y hy]; exact hag (x, y) ((mem_pairsIn T).mpr ⟨hx, hy⟩)
  exact decide_eq_decide.mpr this

/-- **Induction step.** If the sub-models on all sets of `card α - 1` alternatives are mixtures,
the model is a mixture. -/
theorem step (hα : 4 ≤ Fintype.card α) {μ : (ι → Rk α) → Rk α → ℝ} (hM : Model μ)
    (IH : ∀ x : α, IsMixture (subModel (univ.erase x) μ)) : IsMixture μ := by
  unfold IsMixture at IH
  choose wx hwx_nn hwx_sum hwx using IH
  have hne : (univ : Finset α).Nonempty := by
    rw [Finset.univ_nonempty_iff, ← Fintype.card_pos_iff]; omega
  obtain ⟨x0, -⟩ := hne
  -- events inside univ.erase x have the mixture's probability with weights wx x
  have hprob : ∀ x π E, Det (pairsIn (univ.erase x)) E →
      prob μ π E = ∑ k ∈ univ.filter (fun k => E (π k) = true), wx x k :=
    fun x π E hE => prob_of_sub_mixture (univ.erase x) hM (wx x) (hwx x) π E hE
  -- Step 1: the weights do not depend on the omitted alternative
  have hsame : ∀ x, wx x = wx x0 := by
    intro x
    funext k
    have hcard : 1 < ((univ.erase x).erase x0).card := by
      have h1 := Finset.pred_card_le_card_erase (s := univ.erase x) (a := x0)
      rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ] at h1
      omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp hcard
    have hax : a ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha)
    have hbx : b ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hb)
    have hax0 : a ≠ x0 := Finset.ne_of_mem_erase ha
    have hbx0 : b ≠ x0 := Finset.ne_of_mem_erase hb
    obtain ⟨rA, hrA⟩ := exists_rk_above hab
    obtain ⟨rB, hrB⟩ := exists_rk_above (Ne.symm hab)
    let π : ι → Rk α := fun l => if l = k then rA else rB
    have hsel : univ.filter (fun l => (π l).1 a b = true) = {k} := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, π]
      by_cases hl : l = k
      · simp [hl, hrA]
      · simp [hl, PathPinning.asymm rB hrB]
    have e1 := hprob x π (fun σ => σ.1 a b)
      (det_rel ((mem_pairsIn _).mpr ⟨Finset.mem_erase.mpr ⟨hax, Finset.mem_univ a⟩,
        Finset.mem_erase.mpr ⟨hbx, Finset.mem_univ b⟩⟩))
    have e2 := hprob x0 π (fun σ => σ.1 a b)
      (det_rel ((mem_pairsIn _).mpr ⟨Finset.mem_erase.mpr ⟨hax0, Finset.mem_univ a⟩,
        Finset.mem_erase.mpr ⟨hbx0, Finset.mem_univ b⟩⟩))
    simp only [hsel, Finset.sum_singleton] at e1 e2
    exact e1.symm.trans e2
  unfold IsMixture
  refine ⟨wx x0, hwx_nn x0, hwx_sum x0, fun π t => ?_⟩
  -- the top three alternatives of t, and a fourth
  have hU : (univ : Finset α).Nonempty := ⟨x0, Finset.mem_univ _⟩
  obtain ⟨a₁, -, ht1⟩ := exists_top t univ hU
  have hc1 : ((univ : Finset α).erase a₁).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨a₂, ha₂, ht2⟩ := exists_top t _ hc1
  have hc2 : (((univ : Finset α).erase a₁).erase a₂).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha₂,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨a₃, ha₃, ht3⟩ := exists_top t _ hc2
  have hc3 : ((((univ : Finset α).erase a₁).erase a₂).erase a₃).Nonempty := by
    rw [← Finset.card_pos, Finset.card_erase_of_mem ha₃, Finset.card_erase_of_mem ha₂,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]; omega
  obtain ⟨a₄, ha₄⟩ := hc3
  have h21 : a₂ ≠ a₁ := Finset.ne_of_mem_erase ha₂
  have h32 : a₃ ≠ a₂ := Finset.ne_of_mem_erase ha₃
  have h31 : a₃ ≠ a₁ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha₃)
  have h43 : a₄ ≠ a₃ := Finset.ne_of_mem_erase ha₄
  have h42 : a₄ ≠ a₂ := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ha₄)
  have h41 : a₄ ≠ a₁ :=
    Finset.ne_of_mem_erase (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ha₄))
  have t12 : t.1 a₁ a₂ = true := ht1 a₂ (Finset.mem_univ _) h21
  have t23 : t.1 a₂ a₃ = true := ht2 a₃ (Finset.mem_of_mem_erase ha₃) h32
  have t2v : ∀ v, v ≠ a₁ → v ≠ a₂ → t.1 a₂ v = true := fun v h1 h2 =>
    ht2 v (Finset.mem_erase.mpr ⟨h1, Finset.mem_univ v⟩) h2
  have tbetween : ∀ x, t.1 a₁ x = true → t.1 x a₃ = true → x = a₂ := by
    intro x h1x hx3
    by_contra hx2
    have hx1 : x ≠ a₁ := by intro e; rw [e, PathPinning.irrefl] at h1x; exact absurd h1x (by simp)
    have hx3' : x ≠ a₃ := by intro e; rw [e, PathPinning.irrefl] at hx3; exact absurd hx3 (by simp)
    have := ht3 x (Finset.mem_erase.mpr ⟨hx2, Finset.mem_erase.mpr ⟨hx1, Finset.mem_univ x⟩⟩) hx3'
    rw [PathPinning.asymm t hx3] at this; exact absurd this (by simp)
  -- Step 3: the completed profile
  let π' : ι → Rk α := fun k => complete (π k) a₁ a₂ a₃ h31
  -- the probability of t is unchanged by the completion
  let S : Finset (α × α) := pairsIn (univ.erase a₁) ∪ {(a₁, a₂), (a₂, a₁)}
  have eq_t : ∀ σ : Rk α, (∀ p ∈ S, σ.1 p.1 p.2 = t.1 p.1 p.2) → σ = t := by
    intro σ hag
    have off : ∀ u v, u ≠ a₁ → v ≠ a₁ → σ.1 u v = t.1 u v := fun u v hu hv =>
      hag (u, v) (Finset.mem_union_left _ ((mem_pairsIn _).mpr
        ⟨Finset.mem_erase.mpr ⟨hu, Finset.mem_univ u⟩, Finset.mem_erase.mpr ⟨hv, Finset.mem_univ v⟩⟩))
    have s12 : σ.1 a₁ a₂ = true := by
      rw [hag (a₁, a₂) (Finset.mem_union_right _ (by simp))]; exact t12
    have s1v : ∀ v, v ≠ a₁ → σ.1 a₁ v = true := by
      intro v hv
      by_cases hv2 : v = a₂
      · rw [hv2]; exact s12
      · have : σ.1 a₂ v = true := by rw [off a₂ v h21 hv]; exact t2v v hv hv2
        exact PathPinning.trans' σ s12 this
    apply Subtype.ext; funext u v
    by_cases hu : u = a₁ <;> by_cases hv : v = a₁
    · rw [hu, hv, PathPinning.irrefl, PathPinning.irrefl]
    · rw [hu, s1v v hv, ht1 v (Finset.mem_univ v) hv]
    · rw [hv, PathPinning.asymm σ (s1v u hu), PathPinning.asymm t (ht1 u (Finset.mem_univ u) hu)]
    · exact off u v hu hv
  have hdet : Det S (fun σ => decide (σ = t)) := by
    intro σ σ' hag
    by_cases h : σ = t
    · have : σ' = t := eq_t σ' (fun p hp => by rw [← hag p hp, h])
      simp [h, this]
    · have : σ' ≠ t := fun h' => h (eq_t σ (fun p hp => by rw [hag p hp, h']))
      simp [h, this]
  have hagree : AgreeP S π π' := by
    intro k p hp
    rcases Finset.mem_union.mp hp with hp | hp
    · rw [mem_pairsIn] at hp
      exact (complete_off (π k) h31 (Finset.ne_of_mem_erase hp.1)
        (Finset.ne_of_mem_erase hp.2)).symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact (complete_12 (π k) h21 h32 h31).1.symm
      · exact (complete_12 (π k) h21 h32 h31).2.symm
  have hpt : ∀ π0, prob μ π0 (fun σ => decide (σ = t)) = μ π0 t := by
    intro π0
    simp only [prob]
    rw [filter_decide (fun σ => σ = t)]
    rw [show univ.filter (fun σ : Rk α => σ = t) = {t} by ext; simp, Finset.sum_singleton]
  have hmove : μ π t = μ π' t := by
    rw [← hpt π, ← hpt π']; exact hM.compat S _ hdet π π' hagree
  -- Step 4: pinning at the completed profile
  have marg : ∀ (y : α) (ρ : Rk α),
      ∑ σ ∈ univ.filter (fun σ => Agree (univ.erase y) σ ρ), μ π' σ =
      ∑ k ∈ univ.filter (fun k => Agree (univ.erase y) (π' k) ρ), wx x0 k := by
    intro y ρ
    have := hprob y π' _ (det_agree (univ.erase y) ρ)
    simp only [prob] at this
    rw [filter_decide (fun σ => Agree (univ.erase y) σ ρ), hsame y] at this
    rw [this]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    ext k; simp
  have hpin := pin (μ π') (hM.nonneg π') π' (wx x0) (hwx_nn x0)
    (T := univ.erase a₂) (U := univ.erase a₄) (a₁ := a₁) (a₂ := a₂) (a₃ := a₃)
    (fun x => by simp) (Finset.mem_erase.mpr ⟨Ne.symm h41, Finset.mem_univ _⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm h42, Finset.mem_univ _⟩)
    (Finset.mem_erase.mpr ⟨Ne.symm h43, Finset.mem_univ _⟩)
    (Ne.symm h21) (Ne.symm h32) (Ne.symm h31) (marg a₂) (marg a₄)
    (fun k hk => complete_comp (π k) h31 hk) t t12 t23 tbetween
  rw [hmove, hpin]
  apply Finset.sum_congr _ (fun _ _ => rfl)
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, π']
  exact complete_eq (π k) t h31 t12 t23

end Step

/-! ## The induction -/

/-- **Theorem 5′ from the three-alternative case.** -/
theorem mixture_of_base {ι : Type v} [Fintype ι] [DecidableEq ι]
    (base : ∀ (β : Type u) [Fintype β] [DecidableEq β], Fintype.card β = 3 →
      ∀ μ : (ι → Rk β) → Rk β → ℝ, Model μ → IsMixture μ) :
    ∀ (α : Type u) [Fintype α] [DecidableEq α], 3 ≤ Fintype.card α →
      ∀ μ : (ι → Rk α) → Rk α → ℝ, Model μ → IsMixture μ := by
  suffices h : ∀ n, 3 ≤ n → ∀ (α : Type u) [Fintype α] [DecidableEq α], Fintype.card α = n →
      ∀ μ : (ι → Rk α) → Rk α → ℝ, Model μ → IsMixture μ by
    intro α _ _ hα μ hM; exact h _ hα α rfl μ hM
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact base
  | succ n hn ih =>
    intro α _ _ hcard μ hM
    apply step (by omega) hM
    intro x
    apply ih (↥((univ : Finset α).erase x))
    · rw [Fintype.card_coe, Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ, hcard]
      omega
    · exact subModel_model _ hM

end ArrowGeneral
