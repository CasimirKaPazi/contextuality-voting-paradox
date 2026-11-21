/-
  No consistent way to break a cycle (*Map of Voting Paradoxes*, section on
  gluing), in a stronger form than stated there.

  Main theorem (`elects_unbeaten`). Let a rule be a Condorcet extension and
  consistent (reinforcement), with any number of alternatives. Then at every
  profile it elects an alternative that no other alternative beats by
  majority. Consequently, at a profile where every alternative is beaten
  (in particular, with three alternatives, at every profile with a majority
  cycle), no rule is both.
  Finite electorates; the counter-electorates are given explicitly.
  Uses only core Lean, no Mathlib.

  A profile is a list of ballots; joining two electorates is appending their
  lists. A ballot gives each alternative a position (smaller is better),
  so ties are allowed.

  Construction. Let x be the winner at p, let w beat x, and let n be the
  number of voters in p. Take the electorate Y of 2n+1 voters ranking
  x w (rest) and 2n voters ranking w x (rest). Then x is the Condorcet winner
  of Y, so x wins Y; x wins p + p by consistency; so x must win p + p + Y.
  But w is the Condorcet winner of p + p + Y.

  An earlier version of this file assumed a full cycle x ≻ y ≻ w ≻ x. The
  compiler reported the hypothesis y ≻ w as unused: only "someone beats the
  winner" is needed.
-/

namespace Consistency

variable {V A : Type}

def countIf (P : V → Bool) : List V → Nat
  | [] => 0
  | i :: vs =>
    match P i with
    | true => countIf P vs + 1
    | false => countIf P vs

theorem countIf_append (P : V → Bool) :
    ∀ l₁ l₂ : List V, countIf P (l₁ ++ l₂) = countIf P l₁ + countIf P l₂
  | [], l₂ => by simp [countIf]
  | i :: l₁, l₂ => by
    have ih := countIf_append P l₁ l₂
    cases hp : P i <;> simp only [List.cons_append, countIf, hp, ih] <;> omega

theorem countIf_replicate (P : V → Bool) (v : V) :
    ∀ n : Nat, countIf P (List.replicate n v) = if P v = true then n else 0
  | 0 => by simp [countIf]
  | n + 1 => by
    have ih := countIf_replicate P v n
    cases hp : P v <;> simp [List.replicate_succ, countIf, hp, ih]

theorem countIf_le_length (P : V → Bool) : ∀ l : List V, countIf P l ≤ l.length
  | [] => Nat.le_refl 0
  | i :: l => by
    have ih := countIf_le_length P l
    cases hp : P i <;> simp only [countIf, hp, List.length_cons] <;> omega

abbrev Ballot (A : Type) := A → Nat
abbrev Profile (A : Type) := List (Ballot A)

/-- Number of voters ranking a above b. -/
def sup (p : Profile A) (a b : A) : Nat :=
  countIf (fun r => decide (r a < r b)) p

theorem sup_append (p q : Profile A) (a b : A) :
    sup (p ++ q) a b = sup p a b + sup q a b :=
  countIf_append _ p q

theorem sup_le_length (p : Profile A) (a b : A) : sup p a b ≤ p.length :=
  countIf_le_length _ p

/-- a beats b by majority. -/
def beats (p : Profile A) (a b : A) : Prop := sup p b a < sup p a b

/-- x beats every other alternative. -/
def CW (p : Profile A) (x : A) : Prop := ∀ t, t ≠ x → beats p x t

/-- Electing the same winner in two electorates elects it in their union. -/
def Consistent (f : Profile A → A) : Prop :=
  ∀ p q, f p = f q → f (p ++ q) = f p

/-- A Condorcet extension elects the Condorcet winner when there is one. -/
def Condorcet (f : Profile A → A) : Prop :=
  ∀ p x, CW p x → f p = x

variable [DecidableEq A]

/-- The ballot x w (everything else last). -/
def r₁ (x w : A) : Ballot A := fun t => if t = x then 0 else if t = w then 1 else 2
/-- The ballot w x (everything else last). -/
def r₂ (x w : A) : Ballot A := fun t => if t = w then 0 else if t = x then 1 else 2

theorem sup_Y (x w : A) (n k : Nat) (a b : A) :
    sup (List.replicate n (r₁ x w) ++ List.replicate k (r₂ x w)) a b =
      (if r₁ x w a < r₁ x w b then n else 0) + (if r₂ x w a < r₂ x w b then k else 0) := by
  simp only [sup, countIf_append, countIf_replicate, decide_eq_true_eq]

/-- A consistent Condorcet extension never elects an alternative that some
    other alternative beats by majority. Any number of alternatives. -/
theorem elects_unbeaten (f : Profile A → A) (cons : Consistent f) (cond : Condorcet f)
    (p : Profile A) (x w : A) (hxw : x ≠ w) (hfp : f p = x) (hwx : beats p w x) : False := by
  obtain ⟨Y, hYdef⟩ : ∃ Y : Profile A,
      Y = List.replicate (2 * p.length + 1) (r₁ x w) ++
          List.replicate (2 * p.length) (r₂ x w) := ⟨_, rfl⟩
  have hY : ∀ a b, sup Y a b =
      (if r₁ x w a < r₁ x w b then 2 * p.length + 1 else 0) +
      (if r₂ x w a < r₂ x w b then 2 * p.length else 0) := by
    intro a b
    rw [hYdef]
    exact sup_Y x w _ _ a b
  have v₁ : r₁ x w x = 0 := by simp [r₁]
  have v₂ : r₁ x w w = 1 := by simp [r₁, Ne.symm hxw]
  have v₄ : r₂ x w w = 0 := by simp [r₂]
  have v₅ : r₂ x w x = 1 := by simp [r₂, hxw]
  -- x is the Condorcet winner of Y.
  have cwY : CW Y x := by
    intro t ht
    unfold beats
    by_cases htw : t = w
    · rw [htw]
      simp [hY, v₁, v₂, v₄, v₅] <;> omega
    · have g₁ : r₁ x w t = 2 := by simp [r₁, ht, htw]
      have g₂ : r₂ x w t = 2 := by simp [r₂, ht, htw]
      simp [hY, v₁, v₅, g₁, g₂] <;> omega
  have fY : f Y = x := cond Y x cwY
  have fpp : f (p ++ p) = x := by rw [cons p p rfl, hfp]
  have fZ : f (p ++ p ++ Y) = x := by
    rw [cons (p ++ p) Y (by rw [fpp, fY]), fpp]
  -- w is the Condorcet winner of p ++ p ++ Y.
  have cwZ : CW (p ++ p ++ Y) w := by
    intro t ht
    unfold beats at hwx ⊢
    by_cases htx : t = x
    · rw [htx]
      simp [sup_append, hY, v₁, v₂, v₄, v₅] <;> omega
    · have g₁ : r₁ x w t = 2 := by simp [r₁, htx, ht]
      have g₂ : r₂ x w t = 2 := by simp [r₂, htx, ht]
      have hle := sup_le_length p t w
      simp [sup_append, hY, v₂, v₄, g₁, g₂] <;> omega
  have fw : f (p ++ p ++ Y) = w := cond _ w cwZ
  rw [fZ] at fw
  exact hxw fw

/-- If every alternative is beaten by some other alternative at p, no rule is
    both a Condorcet extension and consistent. -/
theorem no_consistent_condorcet_extension (f : Profile A → A)
    (cons : Consistent f) (cond : Condorcet f) (p : Profile A)
    (allBeaten : ∀ x, ∃ w, w ≠ x ∧ beats p w x) : False := by
  obtain ⟨w, hw, hb⟩ := allBeaten (f p)
  exact elects_unbeaten f cons cond p (f p) w (Ne.symm hw) rfl hb

/-- Three alternatives with the majority cycle a ≻ b ≻ c ≻ a: every
    alternative is beaten, so no rule is both. -/
theorem cycle_case (f : Profile A → A) (cons : Consistent f) (cond : Condorcet f)
    (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (three : ∀ t, t = a ∨ t = b ∨ t = c)
    (p : Profile A) (h₁ : beats p a b) (h₂ : beats p b c) (h₃ : beats p c a) : False := by
  apply no_consistent_condorcet_extension f cons cond p
  intro x
  rcases three x with e | e | e
  · exact ⟨c, by rw [e]; exact Ne.symm hac, by rw [e]; exact h₃⟩
  · exact ⟨a, by rw [e]; exact hab, by rw [e]; exact h₁⟩
  · exact ⟨b, by rw [e]; exact hbc, by rw [e]; exact h₂⟩

end Consistency
