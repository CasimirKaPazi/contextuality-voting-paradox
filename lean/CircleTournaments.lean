/-
  *Cycles and Twists*, Section 3, after Proposition 2: which tournaments fit on
  the circle, and the four-alternative example.

  * `circle_locally_transitive`: a tournament placed on the circle ℝ/ℤ, with
    x above y when x is less than half a turn ahead of y, is locally
    transitive: the alternatives one alternative beats are transitively
    ordered, and so are those beating it. (The converse is Rajkumar,
    Veerathu and Mir, Theorem 6; it is not proved here.)
  * `no_circle_placement`: with four alternatives, let d beat every member of
    the cycle a ≻ b ≻ c ≻ a. No placement on the circle realises this.
  * A probabilistic model on the circle that realises it nevertheless, with
    every alternative placed uniformly: here on the seven points k/7, each
    loser uniform and its winner 1, 2 or 3 sevenths of a turn ahead, all 21
    pairs equally likely. Every alternative's marginal is uniform in every
    context (`winner_marginal`, `loser_marginal`), so the model is compatible,
    and every pair in its support has the winner above the loser
    (`support_above`). With the previous theorem: compatible, no global
    section.

  Uses Mathlib.
-/

module

public import Mathlib

@[expose] public section

namespace CircleTournaments

/-- u is above v on the circle ℝ/ℤ: less than half a turn ahead. -/
def Above (u v : ℝ) : Prop := 0 < Int.fract (u - v) ∧ Int.fract (u - v) < 1 / 2

/-- Two points less than half a turn behind (or ahead of) a common reference:
    the comparison between them is the comparison of their offsets. -/
lemma key (s t : ℝ) (hs₀ : 0 < Int.fract s) (hs₁ : Int.fract s < 1 / 2)
    (ht₀ : 0 < Int.fract t) (ht₁ : Int.fract t < 1 / 2) :
    (0 < Int.fract (t - s) ∧ Int.fract (t - s) < 1 / 2) ↔ Int.fract s < Int.fract t := by
  have e : t - s = (Int.fract t - Int.fract s) + ((⌊t⌋ - ⌊s⌋ : ℤ) : ℝ) := by
    have h₁ := Int.floor_add_fract t
    have h₂ := Int.floor_add_fract s
    push_cast
    linarith
  by_cases h : Int.fract s ≤ Int.fract t
  · have hf : Int.fract (t - s) = Int.fract t - Int.fract s := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊t⌋ - ⌊s⌋, ?_⟩
      rw [e]
      push_cast
      ring
    rw [hf]
    constructor
    · rintro ⟨h₁, _⟩
      linarith
    · intro h₁
      constructor <;> linarith
  · push Not at h
    have hf : Int.fract (t - s) = Int.fract t - Int.fract s + 1 := by
      rw [Int.fract_eq_iff]
      refine ⟨by linarith, by linarith, ⌊t⌋ - ⌊s⌋ - 1, ?_⟩
      rw [e]
      push_cast
      ring
    rw [hf]
    constructor
    · rintro ⟨_, h₂⟩
      linarith
    · intro h₁
      exfalso
      linarith

/-- A tournament placed on the circle is locally transitive. -/
theorem circle_locally_transitive {A : Type*} (T : A → A → Prop) (f : A → ℝ)
    (real : ∀ x y, T x y → Above (f x) (f y))
    (tour : ∀ x y, x ≠ y → T x y ∨ T y x) :
    (∀ a x y z, T a x → T a y → T a z → T x y → T y z → T x z) ∧
    (∀ a x y z, T x a → T y a → T z a → T x y → T y z → T x z) := by
  constructor
  · -- what a beats: compare the offsets f a − f t
    intro a x y z hx hy hz hxy hyz
    have kx := real a x hx
    have ky := real a y hy
    have kz := real a z hz
    have cmp : ∀ u v, T a u → T a v → T u v →
        Int.fract (f a - f u) < Int.fract (f a - f v) := by
      intro u v hu hv huv
      have ku := real a u hu
      have kv := real a v hv
      apply (key (f a - f u) (f a - f v) ku.1 ku.2 kv.1 kv.2).mp
      have e : f a - f v - (f a - f u) = f u - f v := by ring
      rw [e]
      exact real u v huv
    have l₁ := cmp x y hx hy hxy
    have l₂ := cmp y z hy hz hyz
    have hne : x ≠ z := by
      intro e
      rw [e] at l₁
      linarith
    rcases tour x z hne with h | h
    · exact h
    · have := cmp z x hz hx h
      exfalso
      linarith
  · -- what beats a: compare the offsets f t − f a
    intro a x y z hx hy hz hxy hyz
    have cmp : ∀ u v, T u a → T v a → T u v →
        Int.fract (f v - f a) < Int.fract (f u - f a) := by
      intro u v hu hv huv
      have ku := real u a hu
      have kv := real v a hv
      apply (key (f v - f a) (f u - f a) kv.1 kv.2 ku.1 ku.2).mp
      have e : f u - f a - (f v - f a) = f u - f v := by ring
      rw [e]
      exact real u v huv
    have l₁ := cmp x y hx hy hxy
    have l₂ := cmp y z hy hz hyz
    have hne : x ≠ z := by
      intro e
      rw [e] at l₁
      linarith
    rcases tour x z hne with h | h
    · exact h
    · have := cmp z x hz hx h
      exfalso
      linarith

/-! ### The four-alternative example -/

inductive Alt where
  | a | b | c | d
  deriving DecidableEq

open Alt

/-- a ≻ b ≻ c ≻ a, and d beats all three. -/
def beatsB : Alt → Alt → Bool
  | .a, .b => true
  | .b, .c => true
  | .c, .a => true
  | .d, .a => true
  | .d, .b => true
  | .d, .c => true
  | _, _ => false

def T (x y : Alt) : Prop := beatsB x y = true

theorem T_tournament : ∀ x y, x ≠ y → T x y ∨ T y x := by
  intro x y h
  cases x <;> cases y <;> simp_all [T, beatsB]

/-- No placement on the circle realises the tournament: what d beats is a
    cycle, not a transitive order. -/
theorem no_circle_placement (f : Alt → ℝ) : ¬ ∀ x y, T x y → Above (f x) (f y) := by
  intro real
  obtain ⟨hout, _⟩ := circle_locally_transitive T f real T_tournament
  have h := hout d a b c (by simp [T, beatsB]) (by simp [T, beatsB]) (by simp [T, beatsB])
    (by simp [T, beatsB]) (by simp [T, beatsB])
  simp [T, beatsB] at h

/-- The probabilistic model: the loser at i/7 for i uniform in 0..6, the
    winner at (i + k)/7 for k uniform in 1..3. Seen on the circle, the winner
    is at the point ((i + k) mod 7)/7, which is uniform: -/
theorem winner_marginal : ∀ j : Fin 7,
    ((Finset.univ : Finset (Fin 7 × Fin 3)).filter
      (fun p => (p.1.val + p.2.val + 1) % 7 = j.val)).card = 3 := by
  decide

/-- and the loser is uniform, by construction: -/
theorem loser_marginal : ∀ j : Fin 7,
    ((Finset.univ : Finset (Fin 7 × Fin 3)).filter (fun p => p.1 = j)).card = 3 := by
  decide

/-- Every pair in the support has the winner above the loser. -/
theorem support_above (i : Fin 7) (k : Fin 3) :
    Above (((i.val : ℝ) + k.val + 1) / 7) ((i.val : ℝ) / 7) := by
  have hk : (k.val : ℝ) ≤ 2 := by
    have : k.val ≤ 2 := by omega
    exact_mod_cast this
  have hk0 : (0 : ℝ) ≤ k.val := by positivity
  have e : ((i.val : ℝ) + k.val + 1) / 7 - (i.val : ℝ) / 7 = ((k.val : ℝ) + 1) / 7 := by ring
  unfold Above
  rw [e, Int.fract_eq_self.mpr ⟨by positivity, by linarith⟩]
  constructor
  · positivity
  · linarith

end CircleTournaments
