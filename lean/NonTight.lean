/-
  Proposition 5 of *Walls and Strategy*: rational diagonal for two-player
  game forms that are not tight.

  A two-player game form g (rows for player 1, columns for player 2) is tight
  if for every set S of outcomes, player 1 can force S or player 2 can force
  its complement. If g is not tight, take such an S where neither holds; let
  player 1 rank S above everything else and player 2 have the reverse
  preference. Then every best reply of player 2 to a row lands outside S, in a
  column where player 1 could have reached S: the zero-sum game has no saddle
  point, and the rational diagonal for player 1 exists. (The same holds for
  player 2 by symmetry.)

  Preferences are strict: injective utility functions, higher is better.
  Outcomes and columns are finite. Uses only core Lean.
-/

namespace NonTight

variable {A B X : Type}

/-- Row a is a best reply of player 1 to column b under utility u. -/
def BR1 (g : A → B → X) (u : X → Nat) (a : A) (b : B) : Prop := ∀ a', u (g a' b) ≤ u (g a b)

/-- Column b is a best reply of player 2 to row a under utility v. -/
def BR2 (g : A → B → X) (v : X → Nat) (a : A) (b : B) : Prop := ∀ b', v (g a b') ≤ v (g a b)

def Injective (f : X → Nat) : Prop := ∀ x y, f x = f y → x = y

/-- Rational diagonal for player 1: strict preferences such that against every
    row some best reply of player 2 makes that row not a best reply. -/
def RationalDiagonal1 (g : A → B → X) : Prop :=
  ∃ u v : X → Nat, Injective u ∧ Injective v ∧ ∀ a, ∃ b, BR2 g v a b ∧ ¬ BR1 g u a b

/-- Player 1 can force S: some row lies entirely in S. -/
def Forces1 (g : A → B → X) (S : X → Bool) : Prop := ∃ a, ∀ b, S (g a b) = true

/-- Player 2 can force T: some column lies entirely in T. -/
def Forces2 (g : A → B → X) (T : X → Bool) : Prop := ∃ b, ∀ a, T (g a b) = true

/-- g is tight: for every S, player 1 forces S or player 2 forces its complement. -/
def Tight (g : A → B → X) : Prop := ∀ S : X → Bool, Forces1 g S ∨ Forces2 g (fun x => !S x)

/-! ### Finite lists -/

theorem exists_max (f : B → Nat) :
    ∀ l : List B, (∃ b, b ∈ l) → ∃ b, b ∈ l ∧ ∀ b', b' ∈ l → f b' ≤ f b
  | [], ⟨_, hb⟩ => by cases hb
  | b :: l, _ => by
    by_cases hl : ∃ c, c ∈ l
    · obtain ⟨m, hm, hmax⟩ := exists_max f l hl
      by_cases h : f b ≤ f m
      · refine ⟨m, by simp [hm], ?_⟩
        intro b' hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with e | e
        · rw [e]
          exact h
        · exact hmax b' e
      · refine ⟨b, by simp, ?_⟩
        intro b' hb'
        simp only [List.mem_cons] at hb'
        rcases hb' with e | e
        · simp [e]
        · have := hmax b' e
          omega
    · refine ⟨b, by simp, ?_⟩
      intro b' hb'
      simp only [List.mem_cons] at hb'
      rcases hb' with e | e
      · simp [e]
      · exact absurd ⟨b', e⟩ hl

variable [DecidableEq X]

/-- Position of the first occurrence of x. -/
def idx : List X → X → Nat
  | [], _ => 0
  | a :: l, x => if a = x then 0 else idx l x + 1

theorem idx_lt : ∀ (l : List X) (x : X), x ∈ l → idx l x < l.length
  | [], _, hx => by cases hx
  | a :: l, x, hx => by
    by_cases hax : a = x
    · simp [idx, hax]
    · have hx' : x ∈ l := by
        rcases List.mem_cons.mp hx with e | e
        · exact absurd e.symm hax
        · exact e
      have := idx_lt l x hx'
      simp [idx, hax]
      omega

theorem idx_inj : ∀ (l : List X) (x y : X), x ∈ l → y ∈ l → idx l x = idx l y → x = y
  | [], _, _, hx, _, _ => by cases hx
  | a :: l, x, y, hx, hy, h => by
    by_cases hax : a = x
    · subst hax
      by_cases hay : a = y
      · exact hay
      · simp [idx, hay] at h
    · by_cases hay : a = y
      · subst hay
        simp [idx, hax] at h
      · simp [idx, hax, hay] at h
        have hx' : x ∈ l := by
          rcases List.mem_cons.mp hx with e | e
          · exact absurd e.symm hax
          · exact e
        have hy' : y ∈ l := by
          rcases List.mem_cons.mp hy with e | e
          · exact absurd e.symm hay
          · exact e
        exact idx_inj l x y hx' hy' h

/-! ### The preferences: S on top, and the reverse -/

/-- Player 1's utility: members of S above non-members, ties broken by position. -/
def uS (allX : List X) (S : X → Bool) (x : X) : Nat :=
  if S x = true then allX.length + idx allX x else idx allX x

theorem uS_in (allX : List X) (hallX : ∀ x, x ∈ allX) (S : X → Bool) (x : X)
    (h : S x = true) : allX.length ≤ uS allX S x ∧ uS allX S x < 2 * allX.length := by
  have := idx_lt allX x (hallX x)
  rw [uS, ite_eq_left h]
  omega

theorem uS_out (allX : List X) (hallX : ∀ x, x ∈ allX) (S : X → Bool) (x : X)
    (h : S x = false) : uS allX S x < allX.length := by
  have := idx_lt allX x (hallX x)
  rw [uS, ite_eq_right (by simp [h])]
  exact this

theorem uS_lt (allX : List X) (hallX : ∀ x, x ∈ allX) (S : X → Bool) (x : X) :
    uS allX S x < 2 * allX.length := by
  cases h : S x with
  | true => exact (uS_in allX hallX S x h).2
  | false =>
    have := uS_out allX hallX S x h
    omega

theorem uS_inj (allX : List X) (hallX : ∀ x, x ∈ allX) (S : X → Bool) :
    Injective (uS allX S) := by
  intro x y hxy
  have ix := idx_lt allX x (hallX x)
  have iy := idx_lt allX y (hallX y)
  apply idx_inj allX x y (hallX x) (hallX y)
  cases hx : S x <;> cases hy : S y <;> simp [uS, hx, hy] at hxy <;> omega

/-- The reverse preference. -/
def vS (allX : List X) (S : X → Bool) (x : X) : Nat := 2 * allX.length - uS allX S x

theorem vS_inj (allX : List X) (hallX : ∀ x, x ∈ allX) (S : X → Bool) :
    Injective (vS allX S) := by
  intro x y h
  have hx := uS_lt allX hallX S x
  have hy := uS_lt allX hallX S y
  unfold vS at h
  exact uS_inj allX hallX S x y (by omega)

/-! ### The theorem -/

/-- If player 1 cannot force S and player 2 cannot force its complement, the
    rational diagonal for player 1 exists. -/
theorem diagonal_of_witness (g : A → B → X) (allX : List X) (hallX : ∀ x, x ∈ allX)
    (allB : List B) (hallB : ∀ b, b ∈ allB) (b₀ : B) (S : X → Bool)
    (h₁ : ∀ a, ∃ b, S (g a b) = false) (h₂ : ∀ b, ∃ a, S (g a b) = true) :
    RationalDiagonal1 g := by
  refine ⟨uS allX S, vS allX S, uS_inj allX hallX S, vS_inj allX hallX S, ?_⟩
  intro a
  obtain ⟨b, _, hb⟩ := exists_max (fun b => vS allX S (g a b)) allB ⟨b₀, hallB b₀⟩
  refine ⟨b, fun b' => hb b' (hallB b'), ?_⟩
  intro hbr
  -- player 2's best reply minimizes u in row a, so it lies outside S
  obtain ⟨b', hb'⟩ := h₁ a
  have hout' := uS_out allX hallX S (g a b') hb'
  have hle := hb b' (hallB b')
  have hlt₁ := uS_lt allX hallX S (g a b)
  have hlt₂ := uS_lt allX hallX S (g a b')
  simp only [vS] at hle
  have hab : uS allX S (g a b) < allX.length := by omega
  -- in that column player 1 could have reached S
  obtain ⟨a', ha'⟩ := h₂ b
  have hin := (uS_in allX hallX S (g a' b) ha').1
  have := hbr a'
  omega

/-- A game form that is not tight has a rational diagonal for player 1. -/
theorem diagonal_of_not_tight (g : A → B → X) (allX : List X) (hallX : ∀ x, x ∈ allX)
    (allB : List B) (hallB : ∀ b, b ∈ allB) (b₀ : B) (hnt : ¬ Tight g) :
    RationalDiagonal1 g := by
  obtain ⟨S, h₁, h₂⟩ : ∃ S : X → Bool, ¬ Forces1 g S ∧ ¬ Forces2 g (fun x => !S x) := by
    apply Classical.byContradiction
    intro hc
    apply hnt
    intro S
    rcases Classical.em (Forces1 g S) with h | h
    · exact Or.inl h
    · rcases Classical.em (Forces2 g (fun x => !S x)) with h' | h'
      · exact Or.inr h'
      · exact absurd ⟨S, h, h'⟩ hc
  apply diagonal_of_witness g allX hallX allB hallB b₀ S
  · intro a
    apply Classical.byContradiction
    intro hc
    apply h₁
    refine ⟨a, fun b => ?_⟩
    cases h : S (g a b) with
    | true => rfl
    | false => exact absurd ⟨b, h⟩ hc
  · intro b
    apply Classical.byContradiction
    intro hc
    apply h₂
    refine ⟨b, fun a => ?_⟩
    cases h : S (g a b) with
    | true => exact absurd ⟨a, h⟩ hc
    | false => simp [h]

end NonTight
