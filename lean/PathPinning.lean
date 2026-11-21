import Mathlib

/-!
# Pinning the probability of a ranking

The combinatorial core (Step 4) of the induction step of Theorem 5′ (*Theorem 5 for any number
of alternatives*, working note): at a completed profile, the probability of a ranking `t` equals
the total weight of the voters whose ranking is `t`.

Setting. Rankings are strict total orders on a finite type `α`, given as Boolean relations
(`σ x y = true` means x is above y). `μ` is any non-negative function on rankings (the social
law at the completed profile). Voters `k : ι` have rankings `r k` and weights `w k ≥ 0`.
The two hypotheses `hT` and `hU` say that the marginals of `μ` on the sets of alternatives `T`
and `U` are the mixture of the voters' restricted rankings; in the note this is Step 1 (the
models on fewer alternatives are mixtures with common weights). The hypothesis `hcomp` is the
completion of Step 3: a voter who ranks `a₂` above both `a₁` and `a₃`, or below both, ranks `a₃`
above `a₁`.

`t` has `a₁` above `a₂` above `a₃` with nothing else between `a₁` and `a₃`; `T` is everything
except `a₂`; `U` contains `a₁`, `a₂`, `a₃`.

Not formalised here: the restriction of an empirical model to fewer alternatives, the use of full
compatibility to pass to the completed profile, and the existence of the completion.
-/

namespace PathPinning

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A strict total order, as a Boolean relation. -/
def IsRank (r : α → α → Bool) : Prop :=
  (∀ x, r x x = false) ∧ (∀ x y z, r x y = true → r y z = true → r x z = true) ∧
  (∀ x y, x ≠ y → r x y = true ∨ r y x = true)

instance (r : α → α → Bool) : Decidable (IsRank r) := by unfold IsRank; infer_instance

/-- Rankings of `α`. -/
abbrev Rk (α : Type*) [Fintype α] [DecidableEq α] := {r : α → α → Bool // IsRank r}

/-- Two rankings agree on the set `S` of alternatives. -/
def Agree (S : Finset α) (σ ρ : Rk α) : Prop := ∀ x ∈ S, ∀ y ∈ S, σ.1 x y = ρ.1 x y

instance (S : Finset α) (σ ρ : Rk α) : Decidable (Agree S σ ρ) := by unfold Agree; infer_instance

lemma irrefl (σ : Rk α) (x : α) : σ.1 x x = false := σ.2.1 x

lemma trans' (σ : Rk α) {x y z : α} (h1 : σ.1 x y = true) (h2 : σ.1 y z = true) :
    σ.1 x z = true := σ.2.2.1 x y z h1 h2

lemma total (σ : Rk α) {x y : α} (h : x ≠ y) : σ.1 x y = true ∨ σ.1 y x = true := σ.2.2.2 x y h

lemma asymm (σ : Rk α) {x y : α} (h : σ.1 x y = true) : σ.1 y x = false := by
  cases h' : σ.1 y x
  · rfl
  · have := trans' σ h h'
    rw [irrefl] at this
    exact absurd this (by simp)

lemma agree_refl (S : Finset α) (σ : Rk α) : Agree S σ σ := fun _ _ _ _ => rfl

/-- A ranking that agrees with `t` off `a₂` and has `a₁` above `a₂` above `a₃` is `t`. -/
lemma eq_of_agree {T : Finset α} {a₁ a₂ a₃ : α} (hT : ∀ x, x ∈ T ↔ x ≠ a₂)
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (_h13 : a₁ ≠ a₃)
    (t : Rk α) (t12 : t.1 a₁ a₂ = true) (t23 : t.1 a₂ a₃ = true)
    (tbetween : ∀ x, t.1 a₁ x = true → t.1 x a₃ = true → x = a₂)
    (σ : Rk α) (hag : Agree T σ t) (s12 : σ.1 a₁ a₂ = true) (s23 : σ.1 a₂ a₃ = true) :
    σ = t := by
  have m1 : a₁ ∈ T := (hT a₁).mpr h12
  have m3 : a₃ ∈ T := (hT a₃).mpr (Ne.symm h23)
  -- comparisons with a₂ agree
  have key : ∀ y, y ≠ a₂ → σ.1 y a₂ = t.1 y a₂ ∧ σ.1 a₂ y = t.1 a₂ y := by
    intro y hy
    have my : y ∈ T := (hT y).mpr hy
    by_cases hy1 : y = a₁
    · subst hy1
      exact ⟨by rw [s12, t12], by rw [asymm σ s12, asymm t t12]⟩
    by_cases hy3 : y = a₃
    · subst hy3
      exact ⟨by rw [asymm σ s23, asymm t t23], by rw [s23, t23]⟩
    rcases total t (show y ≠ a₁ from hy1) with hya | hay
    · -- y above a₁
      have t1 : t.1 y a₂ = true := trans' t hya t12
      have s1 : σ.1 y a₁ = true := by rw [hag y my a₁ m1]; exact hya
      have s2 : σ.1 y a₂ = true := trans' σ s1 s12
      exact ⟨by rw [s2, t1], by rw [asymm σ s2, asymm t t1]⟩
    · -- a₁ above y, so y is below a₃
      have hay3 : t.1 a₃ y = true := by
        rcases total t (show y ≠ a₃ from hy3) with h | h
        · exact absurd (tbetween y hay h) hy
        · exact h
      have t1 : t.1 a₂ y = true := trans' t t23 hay3
      have s1 : σ.1 a₃ y = true := by rw [hag a₃ m3 y my]; exact hay3
      have s2 : σ.1 a₂ y = true := trans' σ s23 s1
      exact ⟨by rw [asymm σ s2, asymm t t1], by rw [s2, t1]⟩
  apply Subtype.ext
  funext x y
  by_cases hx : x = a₂
  · by_cases hy : y = a₂
    · subst hx; subst hy; rw [irrefl, irrefl]
    · subst hx; exact (key y hy).2
  · by_cases hy : y = a₂
    · subst hy; exact (key x hx).1
    · exact hag x ((hT x).mpr hx) y ((hT y).mpr hy)

/-- With `a₁` above `a₃`: either `a₁ > a₂ > a₃`, or `a₂` is above both or below both. -/
lemma three_cases (σ : Rk α) {a₁ a₂ a₃ : α} (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃)
    (s13 : σ.1 a₁ a₃ = true) :
    (σ.1 a₁ a₂ = true ∧ σ.1 a₂ a₃ = true) ∨
      ((σ.1 a₂ a₁ = true ∧ σ.1 a₂ a₃ = true) ∨ (σ.1 a₁ a₂ = true ∧ σ.1 a₃ a₂ = true)) := by
  rcases total σ h12 with h | h
  · rcases total σ h23 with h' | h'
    · exact Or.inl ⟨h, h'⟩
    · exact Or.inr (Or.inr ⟨h, h'⟩)
  · exact Or.inr (Or.inl ⟨h, trans' σ h s13⟩)

/-- **Pinning lemma.** The probability of `t` is the total weight of the voters ranking `t`. -/
theorem pin {ι : Type*} [Fintype ι]
    (μ : Rk α → ℝ) (hμ : ∀ σ, 0 ≤ μ σ) (r : ι → Rk α) (w : ι → ℝ) (hw : ∀ k, 0 ≤ w k)
    {T U : Finset α} {a₁ a₂ a₃ : α} (hT : ∀ x, x ∈ T ↔ x ≠ a₂)
    (hU1 : a₁ ∈ U) (hU2 : a₂ ∈ U) (hU3 : a₃ ∈ U)
    (h12 : a₁ ≠ a₂) (h23 : a₂ ≠ a₃) (h13 : a₁ ≠ a₃)
    (margT : ∀ ρ : Rk α, ∑ σ ∈ Finset.univ.filter (fun σ => Agree T σ ρ), μ σ =
      ∑ k ∈ Finset.univ.filter (fun k => Agree T (r k) ρ), w k)
    (margU : ∀ ρ : Rk α, ∑ σ ∈ Finset.univ.filter (fun σ => Agree U σ ρ), μ σ =
      ∑ k ∈ Finset.univ.filter (fun k => Agree U (r k) ρ), w k)
    (hcomp : ∀ k, ((r k).1 a₂ a₁ = true ∧ (r k).1 a₂ a₃ = true) ∨
      ((r k).1 a₁ a₂ = true ∧ (r k).1 a₃ a₂ = true) → (r k).1 a₃ a₁ = true)
    (t : Rk α) (t12 : t.1 a₁ a₂ = true) (t23 : t.1 a₂ a₃ = true)
    (tbetween : ∀ x, t.1 a₁ x = true → t.1 x a₃ = true → x = a₂) :
    μ t = ∑ k ∈ Finset.univ.filter (fun k => r k = t), w k := by
  have m1 : a₁ ∈ T := (hT a₁).mpr h12
  have m3 : a₃ ∈ T := (hT a₃).mpr (Ne.symm h23)
  have t13 : t.1 a₁ a₃ = true := trans' t t12 t23
  -- (i) only voters ranking t agree with t off a₂
  have voters : Finset.univ.filter (fun k => Agree T (r k) t) =
      Finset.univ.filter (fun k => r k = t) := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hag
      have s13 : (r k).1 a₁ a₃ = true := by rw [hag a₁ m1 a₃ m3]; exact t13
      rcases three_cases (r k) h12 h23 s13 with h | h
      · exact eq_of_agree hT h12 h23 h13 t t12 t23 tbetween (r k) hag h.1 h.2
      · have := hcomp k h
        rw [asymm (r k) s13] at this
        exact absurd this (by simp)
    · intro h; rw [h]; exact agree_refl T t
  -- (ii) every other ranking agreeing with t off a₂ has probability zero
  have others : ∀ σ ∈ Finset.univ.filter (fun σ => Agree T σ t), σ ≠ t → μ σ = 0 := by
    intro σ hσ hne
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    have s13 : σ.1 a₁ a₃ = true := by rw [hσ a₁ m1 a₃ m3]; exact t13
    have hout : (σ.1 a₂ a₁ = true ∧ σ.1 a₂ a₃ = true) ∨
        (σ.1 a₁ a₂ = true ∧ σ.1 a₃ a₂ = true) := by
      rcases three_cases σ h12 h23 s13 with h | h
      · exact absurd (eq_of_agree hT h12 h23 h13 t t12 t23 tbetween σ hσ h.1 h.2) hne
      · exact h
    -- no voter agrees with σ on U
    have hnone : Finset.univ.filter (fun k => Agree U (r k) σ) = ∅ := by
      apply Finset.filter_false_of_mem
      intro k _ hag
      have e21 := hag a₂ hU2 a₁ hU1
      have e23 := hag a₂ hU2 a₃ hU3
      have e12 := hag a₁ hU1 a₂ hU2
      have e32 := hag a₃ hU3 a₂ hU2
      have e13 := hag a₁ hU1 a₃ hU3
      have hk : ((r k).1 a₂ a₁ = true ∧ (r k).1 a₂ a₃ = true) ∨
          ((r k).1 a₁ a₂ = true ∧ (r k).1 a₃ a₂ = true) := by
        rw [e21, e23, e12, e32]; exact hout
      have h31 := hcomp k hk
      have k13 : (r k).1 a₁ a₃ = true := by rw [e13]; exact s13
      rw [asymm (r k) k13] at h31
      exact absurd h31 (by simp)
    have hle : μ σ ≤ ∑ σ' ∈ Finset.univ.filter (fun σ' => Agree U σ' σ), μ σ' :=
      Finset.single_le_sum (fun σ' _ => hμ σ')
        (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact agree_refl U σ)
    rw [margU σ, hnone, Finset.sum_empty] at hle
    exact le_antisymm hle (hμ σ)
  have hsingle : ∑ σ ∈ Finset.univ.filter (fun σ => Agree T σ t), μ σ = μ t :=
    Finset.sum_eq_single_of_mem t
      (by simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact agree_refl T t) others
  rw [← hsingle, margT t, voters]

end PathPinning
