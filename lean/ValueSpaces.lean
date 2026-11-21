/-
  Propositions 1–4 of *Cycles and Twists*: a preference cycle placed
  in three value spaces (bounded line, circle, unbounded line), and the
  winding number. General statements, any length of cycle.
  Uses only core Lean, no Mathlib.
-/

namespace ValueSpaces

/-! ### Proposition 1: bounded line -/

/-- A model of a cycle on a bounded line has no compatible realisation.

  Alternatives form a type `A`; `prev a` is the alternative that beats `a`
  on the cycle. The context of the pair {prev a, a} is given by `S a`:
  `S a x y` means prev a may sit at value x while a sits at value y.
  Values are natural numbers bounded by `K`, which covers every finite chain.

  The proof uses only that every alternative has some alternative beating it.
  For a finite set of alternatives this is the same as containing a cycle;
  the theorem does not need finiteness of `A` or that `prev` closes up. -/
theorem bounded_line {A : Type} (prev : A → A) (S : A → Nat → Nat → Prop) (K : Nat)
    (realises : ∀ a x y, S a x y → y < x)
    (compatible : ∀ a x, (∃ y, S a x y) ↔ (∃ y', S (prev a) y' x))
    (nonempty : ∃ a x y, S a x y)
    (bounded : ∀ a x y, S a x y → x ≤ K ∧ y ≤ K) : False := by
  -- Climbing: for every k some alternative is allowed a value of at least k.
  have climb : ∀ k : Nat, ∃ a y, (∃ x, S a x y) ∧ k ≤ y := by
    intro k
    induction k with
    | zero =>
      obtain ⟨a, x, y, h⟩ := nonempty
      exact ⟨a, y, ⟨x, h⟩, Nat.zero_le y⟩
    | succ k ih =>
      obtain ⟨a, y, ⟨x, h⟩, hk⟩ := ih
      have hxy := realises a x y h
      obtain ⟨y', h'⟩ := (compatible a x).mp ⟨y, h⟩
      exact ⟨prev a, x, ⟨y', h'⟩, by omega⟩
  obtain ⟨a, y, ⟨x, h⟩, hk⟩ := climb (K + 1)
  have hb := (bounded a x y h).2
  omega

/-! ### Proposition 3: unbounded line -/

/-- The model on the integers: in the context of a pair with x ≻ y, every
    placement with x above y is allowed. -/
def lineModel (x y : Int) : Prop := y < x

/-- The model is compatible: in every context every alternative may take
    every value. -/
theorem lineModel_compatible :
    ∀ x : Int, (∃ y, lineModel x y) ↔ (∃ y', lineModel y' x) := by
  intro x
  constructor
  · intro _
    exact ⟨x + 1, show x < x + 1 by omega⟩
  · intro _
    exact ⟨x - 1, show x - 1 < x by omega⟩

/-- It has no global section: there is no placement a₀ > a₁ > … > aₙ > a₀
    of a cycle on the line. -/
theorem lineModel_no_global_section (n : Nat) (f : Nat → Int)
    (step : ∀ i, i < n → lineModel (f i) (f (i + 1)))
    (close : lineModel (f n) (f 0)) : False := by
  have down : ∀ k, k ≤ n → f k ≤ f 0 := by
    intro k
    induction k with
    | zero => intro _; omega
    | succ k ih =>
      intro hk
      have h1 := ih (by omega)
      have h2 : f (k + 1) < f k := step k (by omega)
      omega
  have h3 := down n (Nat.le_refl n)
  have h4 : f 0 < f n := close
  omega

/-! ### Proposition 2: circle -/

/-- The circle with m points (ℤ/m): u is above v when u is less than half a
    turn ahead of v. -/
def Above (m u v : Nat) : Prop :=
  0 < (u + m - v) % m ∧ 2 * ((u + m - v) % m) < m

/-- A cycle of n ≥ 3 alternatives has a global section on the circle:
    place alternative i at n − 1 − i. Each step, including the closing step
    from the last alternative back to the first, is one notch. -/
theorem circle_section (n : Nat) (hn : 3 ≤ n) :
    (∀ i, i + 1 < n → Above n (n - 1 - i) (n - 1 - (i + 1))) ∧
    Above n (n - 1 - (n - 1)) (n - 1 - 0) := by
  constructor
  · intro i hi
    have e : n - 1 - i + n - (n - 1 - (i + 1)) = n + 1 := by omega
    unfold Above
    rw [e, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega : 1 < n)]
    omega
  · have e : n - 1 - (n - 1) + n - (n - 1 - 0) = 1 := by omega
    unfold Above
    rw [e, Nat.mod_eq_of_lt (by omega : 1 < n)]
    omega

/-! ### Proposition 4: the winding number -/

/-- Three alternatives on a circle of circumference m. The steps of the closed
    walk a → b → c → a are d₁, d₂, d₃, each reduced to (−m/2, m/2) and nonzero
    (all pairs comparable); a positive step means the current alternative is
    above the next. Since the walk closes, d₁ + d₂ + d₃ = w · m.
    A cycle (all steps positive, or all negative) has w = ±1; a transitive
    tournament (mixed signs) has w = 0. -/
theorem winding (m d₁ d₂ d₃ w : Int) (hm : 0 < m)
    (b₁ : -m < 2 * d₁ ∧ 2 * d₁ < m) (b₂ : -m < 2 * d₂ ∧ 2 * d₂ < m)
    (b₃ : -m < 2 * d₃ ∧ 2 * d₃ < m)
    (closes : d₁ + d₂ + d₃ = w * m) :
    ((0 < d₁ ∧ 0 < d₂ ∧ 0 < d₃) → w = 1) ∧
    ((d₁ < 0 ∧ d₂ < 0 ∧ d₃ < 0) → w = -1) ∧
    ((d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ d₃ ≠ 0) → ¬(0 < d₁ ∧ 0 < d₂ ∧ 0 < d₃) →
      ¬(d₁ < 0 ∧ d₂ < 0 ∧ d₃ < 0) → w = 0) := by
  have hm' : (0 : Int) ≤ m := by omega
  refine ⟨?_, ?_, ?_⟩
  · intro _
    by_cases h0 : w ≤ 0
    · have := Int.mul_le_mul_of_nonneg_right h0 hm'
      omega
    · by_cases h2 : 2 ≤ w
      · have := Int.mul_le_mul_of_nonneg_right h2 hm'
        omega
      · omega
  · intro _
    by_cases h0 : 0 ≤ w
    · have := Int.mul_le_mul_of_nonneg_right h0 hm'
      omega
    · by_cases h2 : w ≤ -2
      · have := Int.mul_le_mul_of_nonneg_right h2 hm'
        omega
      · omega
  · intro _ _ _
    by_cases h1 : 1 ≤ w
    · have := Int.mul_le_mul_of_nonneg_right h1 hm'
      omega
    · by_cases h2 : w ≤ -1
      · have := Int.mul_le_mul_of_nonneg_right h2 hm'
        omega
      · omega

/-- A placement on the circle lifts to the line (the steps close up there
    too) exactly when w = 0. -/
theorem lifts_iff (m d₁ d₂ d₃ w : Int) (hm : 0 < m)
    (closes : d₁ + d₂ + d₃ = w * m) :
    d₁ + d₂ + d₃ = 0 ↔ w = 0 := by
  have hm' : (0 : Int) ≤ m := by omega
  constructor
  · intro _
    by_cases h1 : 1 ≤ w
    · have := Int.mul_le_mul_of_nonneg_right h1 hm'
      omega
    · by_cases h2 : w ≤ -1
      · have := Int.mul_le_mul_of_nonneg_right h2 hm'
        omega
      · omega
  · intro h
    subst h
    rw [Int.zero_mul] at closes
    exact closes

end ValueSpaces
