/-
  The second part of Proposition 2 of *The Global Form*
  (`notes/global-form.md`, Section 4): for an empirical model of Arrow's
  scenario with three alternatives (full compatibility and unanimity, as in
  *Four Levels*), the real degrees are the weights of its mixture of
  dictatorships; they sum to 1 and do not depend on the context. With
  anonymity every real degree is 1/n.

  The bridge. `GlobalForm.lean` and `GlobalFormReal.lean` name the six
  rankings of a, b, c by their positions on the hexagon abc, bac, bca, cba,
  cab, acb; Arrow's scenario (`ArrowGeneral.Model`) uses rankings of
  `Fin 3` as Boolean relations (`PathPinning.Rk`). `hexG` maps each position
  to its ranking; it is a bijection (`hexG_bij`), and its comparisons on ab,
  ac, bc are the bits of `GlobalForm.bit` (`hexG_bit`), so it is the
  hexagon of `GlobalForm`. `toHex μ` reads an Arrow rule on the hexagon.

  * `prop2_model`: Theorem 5′ (`ArrowBase.theorem5'`) makes the model a
    mixture of dictatorships with weights λ; read on the hexagon this is
    `mixDA (dictW λ)`, and `rdeg_dict` gives real degree λ_i at every
    context.
  * `prop2_anonymous`: an anonymous model gives every voter the same weight,
    so every real degree is 1/n: random dictatorship is the only anonymous
    empirical model, and its degrees are the real point (1/n, …, 1/n) on the
    line Σ deg_i = 1.

  Not formalised: that the real degree is the expected winding of every
  compatible joint draw along the loop.
-/

module

public import Mathlib
public import GlobalFormReal
public import ArrowBase
public import Rankings

@[expose] public section

open Finset GlobalFormReal

namespace RealDegreeBridge

/-! ### The hexagon of `GlobalForm` as rankings of `Fin 3` -/

/-- The top at each position: abc, bac, bca, cba, cab, acb. -/
def topG : Fin 6 → Fin 3 := ![0, 1, 1, 2, 2, 0]
/-- The second at each position. -/
def secG : Fin 6 → Fin 3 := ![1, 0, 2, 1, 0, 2]

/-- The place of x at position p: 0 for the top, 1 for the second, 2 for the bottom. -/
def posG (p : Fin 6) (x : Fin 3) : ℕ := if x = topG p then 0 else if x = secG p then 1 else 2

lemma posG_inj : ∀ p, Function.Injective (posG p) := by decide

/-- The ranking at position p. -/
def hexG (p : Fin 6) : PathPinning.Rk (Fin 3) := Rankings.toRk (posG p) (posG_inj p)

lemma hexG_inj : Function.Injective hexG := by decide +kernel

lemma hexG_surj : Function.Surjective hexG := by decide +kernel

lemma hexG_bij : Function.Bijective hexG := ⟨hexG_inj, hexG_surj⟩

/-- The comparisons of `hexG p` on ab, ac, bc are the bits of `GlobalForm`. -/
lemma hexG_bit : ∀ p : Fin 6, (hexG p).1 0 1 = GlobalForm.bit 0 p ∧
    (hexG p).1 0 2 = GlobalForm.bit 1 p ∧ (hexG p).1 1 2 = GlobalForm.bit 2 p := by
  decide +kernel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- An Arrow rule read on the hexagon. -/
def toHex (μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ) :
    (ι → Fin 6) → Fin 6 → ℝ :=
  fun π y => μ (fun i => hexG (π i)) (hexG y)

/-! ### Proposition 2 -/

omit [DecidableEq ι] in
/-- A mixture of dictatorships of `ArrowGeneral`, read on the hexagon, is the
    mixture `mixDA (dictW w)` of `GlobalFormReal`. -/
lemma toHex_mixture {μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ}
    {w : ι → ℝ} (hw : ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k) :
    toHex μ = mixDA (dictW w) := by
  funext π y
  show μ (fun i => hexG (π i)) (hexG y) = mixDA (dictW w) π y
  rw [hw, sum_filter]
  unfold mixDA
  refine sum_congr rfl fun k _ => ?_
  by_cases h : π k = y
  · simp [dictW, comp, ind, h]
  · simp [dictW, comp, ind, h, Ne.symm h, hexG_inj.eq_iff]

/-- **Proposition 2, second part.** For an empirical model of Arrow's
    scenario with three alternatives, the real degrees are the weights of its
    mixture of dictatorships: non-negative, summing to 1, the same at every
    context. -/
theorem prop2_model (μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ)
    (hM : ArrowGeneral.Model μ) :
    ∃ lam : ι → ℝ, (∀ k, 0 ≤ lam k) ∧ ∑ k, lam k = 1 ∧
      ∀ i c, rdeg (toHex μ) i c = lam i := by
  obtain ⟨w, hw0, hw1, hw⟩ := ArrowBase.theorem5' (Fin 3) (by simp) μ hM
  refine ⟨w, hw0, hw1, fun i c => ?_⟩
  rw [toHex_mixture hw]
  exact rdeg_dict w i c

/-- Anonymity: permuting the voters does not change the lottery. -/
def Anonymous (μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ) : Prop :=
  ∀ (e : Equiv.Perm ι) π, μ (fun i => π (e i)) = μ π

/-- The weight of voter k in a mixture of dictatorships is the probability of
    k's ranking when k alone holds it. -/
lemma weight_eq {μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ} {w : ι → ℝ}
    (hw : ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k) (k : ι) :
    w k = μ (Function.update (fun _ => hexG 1) k (hexG 0)) (hexG 0) := by
  rw [hw]
  have : univ.filter (fun j => Function.update (fun _ => hexG 1) k (hexG 0) j = hexG 0) = {k} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · intro h
      by_contra hjk
      rw [Function.update_of_ne hjk] at h
      exact absurd (hexG_inj h) (by decide)
    · rintro rfl
      simp
  rw [this, sum_singleton]

/-- **Anonymity.** An anonymous empirical model of Arrow's scenario with three
    alternatives gives every voter real degree 1/n, at every context. -/
theorem prop2_anonymous (μ : (ι → PathPinning.Rk (Fin 3)) → PathPinning.Rk (Fin 3) → ℝ)
    (hM : ArrowGeneral.Model μ) (hA : Anonymous μ) (i : ι) (c : ι → Fin 6) :
    rdeg (toHex μ) i c = 1 / Fintype.card ι := by
  obtain ⟨w, -, hw1, hw⟩ := ArrowBase.theorem5' (Fin 3) (by simp) μ hM
  -- all weights are equal
  have heq : ∀ k k', w k = w k' := by
    intro k k'
    have hswap : (fun j => Function.update (fun _ => hexG 1) k' (hexG 0) (Equiv.swap k k' j)) =
        Function.update (fun _ => hexG 1) k (hexG 0) := by
      funext j
      simp only [Function.update_apply, Equiv.swap_apply_def]
      split_ifs <;> simp_all
    rw [weight_eq hw k, weight_eq hw k', ← hswap,
      hA (Equiv.swap k k') (Function.update (fun _ => hexG 1) k' (hexG 0))]
  have hcard : (Fintype.card ι : ℝ) * w i = 1 := by
    have h := sum_congr rfl fun k (_ : k ∈ (univ : Finset ι)) => (heq i k).symm
    rw [sum_const, card_univ, nsmul_eq_mul] at h
    linarith
  have hne : (Fintype.card ι : ℝ) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hcard
    exact zero_ne_one hcard
  rw [toHex_mixture hw, rdeg_dict]
  field_simp
  linarith

end RealDegreeBridge
