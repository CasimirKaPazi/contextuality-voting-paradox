/-
  *Cycles and Twists*, Section 3, remark (d): the contextuality of
  Proposition 3 is possibilistic only.

  If every alternative of a finite set is beaten by some alternative of the
  set, no family of probability distributions on the real line places the
  winner of each such pair above the loser, even if only the distributions of
  single alternatives are required to agree between contexts.

  Proof: compare expectations of arctan, a bounded strictly increasing
  function. If a' beats a, then arctan(a') − arctan(a) is positive almost
  surely and bounded, so its expectation is positive. An alternative with the
  largest expectation is beaten by one with a larger expectation.

  Encoding. The alternatives form a finite type A; `beat a` is an alternative
  beating a. The context of the pair {beat a, a} is a probability measure
  `ν a` on ℝ × ℝ, first coordinate the placement of `beat a`, second that of
  a. Each alternative a has one distribution `μ a`, and every context
  containing a has it as the marginal of a (weak compatibility).
  Uses Mathlib.
-/

module

public import Mathlib

@[expose] public section

open MeasureTheory

namespace ProbLine

/-- arctan of a measurable function is integrable for a probability measure,
    being bounded by π/2. -/
lemma integrable_arctan {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (f : Ω → ℝ) (hf : Measurable f) :
    Integrable (fun ω => Real.arctan (f ω)) P := by
  refine Integrable.mono' (integrable_const (Real.pi / 2)) ?_ ?_
  · exact (Real.continuous_arctan.measurable.comp hf).aestronglyMeasurable
  · refine ae_of_all _ (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩

/-- Remark (d). -/
theorem no_probabilistic_model {A : Type*} [Finite A] [Nonempty A]
    (beat : A → A)
    (μ : A → Measure ℝ)
    (ν : A → Measure (ℝ × ℝ)) (hν : ∀ a, IsProbabilityMeasure (ν a))
    (hfst : ∀ a, (ν a).map Prod.fst = μ (beat a))
    (hsnd : ∀ a, (ν a).map Prod.snd = μ a)
    (habove : ∀ a, ∀ᵐ p ∂(ν a), p.2 < p.1) : False := by
  let m : A → ℝ := fun a => ∫ x, Real.arctan x ∂(μ a)
  have step : ∀ a, m a < m (beat a) := by
    intro a
    have := hν a
    have h₁ : m (beat a) = ∫ p, Real.arctan p.1 ∂(ν a) := by
      show ∫ x, Real.arctan x ∂(μ (beat a)) = _
      rw [← hfst a, integral_map measurable_fst.aemeasurable
        Real.continuous_arctan.aestronglyMeasurable]
    have h₂ : m a = ∫ p, Real.arctan p.2 ∂(ν a) := by
      show ∫ x, Real.arctan x ∂(μ a) = _
      rw [← hsnd a, integral_map measurable_snd.aemeasurable
        Real.continuous_arctan.aestronglyMeasurable]
    rw [h₁, h₂]
    have i₁ := integrable_arctan (ν a) Prod.fst measurable_fst
    have i₂ := integrable_arctan (ν a) Prod.snd measurable_snd
    rw [← sub_pos, ← integral_sub i₁ i₂]
    have hpos : ∀ᵐ p ∂(ν a), 0 < Real.arctan p.1 - Real.arctan p.2 :=
      (habove a).mono (fun p hp => sub_pos.mpr (Real.arctan_strictMono hp))
    rw [integral_pos_iff_support_of_nonneg_ae (hpos.mono fun p hp => hp.le) (i₁.sub i₂)]
    have hnull : (ν a) {p | ¬ (0 < Real.arctan p.1 - Real.arctan p.2)} = 0 :=
      ae_iff.mp hpos
    rw [pos_iff_ne_zero]
    intro h₀
    have hc : (ν a) (Function.support
        fun p : ℝ × ℝ => Real.arctan p.1 - Real.arctan p.2)ᶜ = 0 := by
      refine measure_mono_null (fun p hp => ?_) hnull
      simp only [Set.mem_compl_iff, Function.mem_support, not_not] at hp
      show ¬ (0 < Real.arctan p.1 - Real.arctan p.2)
      rw [hp]
      exact lt_irrefl 0
    have hu := measure_union_null h₀ hc
    rw [Set.union_compl_self, measure_univ] at hu
    exact one_ne_zero hu
  obtain ⟨a, ha⟩ := Finite.exists_max m
  exact absurd (ha (beat a)) (not_le.mpr (step a))

end ProbLine
