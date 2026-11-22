import Mathlib
import PathPinning
import JointDraws

/-!
# One encoding of rankings

The Arrow files encode a ranking as a strict total order `PathPinning.Rk α` (a Boolean relation,
`σ.1 a b = true` meaning that `a` is above `b`). `JointDraws.lean` encodes it as an injective map
`α → ℕ` (`σ a < σ b` meaning that `a` is above `b`). This file connects the two and states the
joint-draw theorem for `Rk`, which is a finite type and so can serve as the ballot type of a
scenario.

* `pos σ a`: the number of alternatives above `a`; `pos σ a < pos σ b ↔ σ.1 a b = true`, and
  `pos σ` is injective.
* `toRk σ`: the ranking of an injective map; `toRk (pos ρ) = ρ`.
* `prop1R`: a one-voter scheme on `Rk α` with nonnegative lotteries is SD-strategy-proof exactly
  when every two ballots admit a joint draw on admissible pairs (Proposition 1 of
  *Gibbard–Satterthwaite as a Scenario*, from `JointDraws.prop1`).
-/

open Finset

namespace Rankings

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Positions -/

/-- The alternatives above `a`. -/
def above (σ : PathPinning.Rk α) (a : α) : Finset α := univ.filter (fun c => σ.1 c a = true)

/-- The position of `a`: the number of alternatives above it. -/
def pos (σ : PathPinning.Rk α) (a : α) : ℕ := (above σ a).card

lemma pos_lt_of (σ : PathPinning.Rk α) {a b : α} (h : σ.1 a b = true) : pos σ a < pos σ b := by
  apply card_lt_card
  refine (ssubset_iff_of_subset ?_).mpr ⟨a, ?_, ?_⟩
  · intro c hc
    simp only [above, mem_filter, mem_univ, true_and] at hc ⊢
    exact PathPinning.trans' σ hc h
  · simp [above, h]
  · simp [above, PathPinning.irrefl]

lemma pos_lt_iff (σ : PathPinning.Rk α) (a b : α) : pos σ a < pos σ b ↔ σ.1 a b = true := by
  constructor
  · intro h
    by_cases hab : a = b
    · rw [hab] at h; exact absurd h (lt_irrefl _)
    · rcases PathPinning.total σ hab with h1 | h1
      · exact h1
      · have := pos_lt_of σ h1
        omega
  · exact pos_lt_of σ

lemma pos_inj (σ : PathPinning.Rk α) : Function.Injective (pos σ) := by
  intro a b h
  by_contra hab
  rcases PathPinning.total σ hab with h1 | h1
  · have := pos_lt_of σ h1; omega
  · have := pos_lt_of σ h1; omega

/-! ### From injective maps to rankings -/

/-- The ranking of an injective map to `ℕ`. -/
def toRk (σ : α → ℕ) (hσ : Function.Injective σ) : PathPinning.Rk α :=
  ⟨fun a b => decide (σ a < σ b), by
    unfold PathPinning.IsRank
    refine ⟨fun x => by simp, fun x y z h1 h2 => ?_, fun x y hxy => ?_⟩
    · simp only [decide_eq_true_eq] at h1 h2 ⊢
      omega
    · have : σ x ≠ σ y := fun e => hxy (hσ e)
      rcases lt_or_gt_of_ne this with h | h
      · left; simpa using h
      · right; simpa using h⟩

lemma toRk_apply (σ : α → ℕ) (hσ : Function.Injective σ) (a b : α) :
    (toRk σ hσ).1 a b = true ↔ σ a < σ b := by
  simp [toRk]

lemma toRk_pos (ρ : PathPinning.Rk α) : toRk (pos ρ) (pos_inj ρ) = ρ := by
  apply Subtype.ext
  funext a b
  show decide (pos ρ a < pos ρ b) = ρ.1 a b
  by_cases h : ρ.1 a b = true
  · rw [h]; exact decide_eq_true ((pos_lt_iff ρ a b).mpr h)
  · have h' : ρ.1 a b = false := by simpa using h
    rw [h']
    exact decide_eq_false (fun e => h ((pos_lt_iff ρ a b).mp e))

/-! ### The joint-draw theorem on `Rk` -/

/-- `U` is an upper set of `ρ`. -/
def UpR (ρ : PathPinning.Rk α) (U : Finset α) : Prop :=
  ∀ a b, b ∈ U → ρ.1 a b = true → a ∈ U

/-- SD-strategy-proofness of a one-voter scheme on `Rk α`. -/
def SDSPR (L : PathPinning.Rk α → α → ℝ) : Prop :=
  ∀ ρ τ : PathPinning.Rk α, ∀ U, UpR ρ U → ∑ a ∈ U, L τ a ≤ ∑ a ∈ U, L ρ a

/-- Admissible pair: outcome `a` under ballot `ρ`, `b` under `τ`, no gain by switching either way. -/
def AdmR (ρ τ : PathPinning.Rk α) (a b : α) : Prop :=
  (a = b ∨ ρ.1 a b = true) ∧ (b = a ∨ τ.1 b a = true)

/-- A joint draw of `p` (at `ρ`) and `q` (at `τ`) on admissible pairs. -/
def JointDrawR (ρ τ : PathPinning.Rk α) (p q : α → ℝ) : Prop :=
  ∃ J : α → α → ℝ, (∀ a b, 0 ≤ J a b) ∧ (∀ a, ∑ b, J a b = p a) ∧ (∀ b, ∑ a, J a b = q b) ∧
    (∀ a b, J a b ≠ 0 → AdmR ρ τ a b)

/-- A scheme on `Rk α` read as a scheme on injective maps (arbitrary elsewhere). -/
noncomputable def lift (L : PathPinning.Rk α → α → ℝ) (σ : α → ℕ) : α → ℝ := by
  classical
  exact if h : Function.Injective σ then L (toRk σ h) else fun _ => 0

lemma lift_of_inj (L : PathPinning.Rk α → α → ℝ) {σ : α → ℕ} (hσ : Function.Injective σ) :
    lift L σ = L (toRk σ hσ) := by
  unfold lift
  simp [hσ]

lemma lift_nonneg {L : PathPinning.Rk α → α → ℝ} (hL0 : ∀ ρ a, 0 ≤ L ρ a) (σ : α → ℕ) (a : α) :
    0 ≤ lift L σ a := by
  by_cases hσ : Function.Injective σ
  · rw [lift_of_inj L hσ]; exact hL0 _ a
  · unfold lift
    simp [hσ]

lemma sdsp_lift {L : PathPinning.Rk α → α → ℝ} (h : SDSPR L) : JointDraws.SDSP (lift L) := by
  intro σ τ hσ hτ U hU
  rw [lift_of_inj L hσ, lift_of_inj L hτ]
  exact h _ _ U (fun a b hb hab => hU a b hb ((toRk_apply σ hσ a b).mp hab))

lemma lift_pos (L : PathPinning.Rk α → α → ℝ) (ρ : PathPinning.Rk α) :
    lift L (pos ρ) = L ρ := by
  rw [lift_of_inj L (pos_inj ρ), toRk_pos]

/-- Proposition 1 of *Gibbard–Satterthwaite as a Scenario* for ballots in `Rk α`. -/
theorem prop1R {L : PathPinning.Rk α → α → ℝ} (hL0 : ∀ ρ a, 0 ≤ L ρ a) :
    SDSPR L ↔ ∀ ρ τ : PathPinning.Rk α, JointDrawR ρ τ (L ρ) (L τ) := by
  constructor
  · intro hsd ρ τ
    have hJ := JointDraws.joint_of_sd (lift_nonneg hL0) (sdsp_lift hsd) (pos_inj ρ) (pos_inj τ)
    rw [lift_pos, lift_pos] at hJ
    obtain ⟨J, h0, hr, hc, hs⟩ := hJ
    refine ⟨J, h0, hr, hc, fun a b hab => ?_⟩
    obtain ⟨h1, h2⟩ := hs a b hab
    constructor
    · rcases lt_or_eq_of_le h1 with h | h
      · exact Or.inr ((pos_lt_iff ρ a b).mp h)
      · exact Or.inl (pos_inj ρ h)
    · rcases lt_or_eq_of_le h2 with h | h
      · exact Or.inr ((pos_lt_iff τ b a).mp h)
      · exact Or.inl (pos_inj τ h)
  · intro h ρ τ U hU
    obtain ⟨J, h0, hr, hc, hs⟩ := h ρ τ
    have hJ : JointDraws.JointDraw (pos ρ) (pos τ) (L ρ) (L τ) := by
      refine ⟨J, h0, hr, hc, fun a b hab => ?_⟩
      obtain ⟨h1, h2⟩ := hs a b hab
      constructor
      · rcases h1 with e | e
        · rw [e]
        · exact (pos_lt_of ρ e).le
      · rcases h2 with e | e
        · rw [e]
        · exact (pos_lt_of τ e).le
    exact JointDraws.sd_of_joint (pos_inj ρ) hJ U
      (fun a b hb hab => hU a b hb ((pos_lt_iff ρ a b).mp hab))

end Rankings
