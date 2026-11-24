/-
  Two short facts about profiles from the companion drafts:
  * *Cycles and Twists*, Section 3, remark (b): the classical bound p(a ≻ b) + p(b ≻ c) + p(c ≻ a) ≤ 2,
    for any profile, attained by the Condorcet profile;
  * *Walls and Strategy*, observation in Section 2: no deterministic rule on three alternatives
    and three voters is anonymous and neutral.
  Uses only core Lean, no Mathlib.
-/

module

@[expose] public section

namespace ProfileFacts

variable {V A : Type}

def countIf (P : V → Bool) : List V → Nat
  | [] => 0
  | i :: vs =>
    match P i with
    | true => countIf P vs + 1
    | false => countIf P vs

/-- If no voter satisfies all three of P, Q, R, the three counts add up to
    at most twice the number of voters. -/
theorem three_counts (P Q R : V → Bool)
    (h : ∀ i, ¬(P i = true ∧ Q i = true ∧ R i = true)) :
    ∀ vs : List V, countIf P vs + countIf Q vs + countIf R vs ≤ 2 * vs.length
  | [] => by simp [countIf]
  | i :: vs => by
    have ih := three_counts P Q R h vs
    have hi := h i
    cases hp : P i <;> cases hq : Q i <;> cases hr : R i <;>
      simp only [countIf, hp, hq, hr, List.length_cons] <;>
      first
      | omega
      | exact absurd ⟨hp, hq, hr⟩ hi

/-- Number of voters ranking a above b (ballots give positions; ties allowed). -/
def sup (p : List (A → Nat)) (a b : A) : Nat :=
  countIf (fun r => decide (r a < r b)) p

/-- *Cycles and Twists*, Section 3, remark (b): no ballot satisfies all of a ≻ b, b ≻ c, c ≻ a, so over any
    profile the three pairwise supports add up to at most twice the number of
    voters. Holds also for ballots with ties. -/
theorem boole_bound (p : List (A → Nat)) (a b c : A) :
    sup p a b + sup p b c + sup p c a ≤ 2 * p.length :=
  three_counts _ _ _ (fun r ⟨h₁, h₂, h₃⟩ => by
    simp only [decide_eq_true_eq] at h₁ h₂ h₃
    omega) p

/-- The Condorcet profile abc, bca, cab, as positions of a = 0, b = 1, c = 2. -/
def condorcetBallots : List (Nat → Nat) :=
  [fun t => t, fun t => (t + 2) % 3, fun t => (t + 1) % 3]

/-- It attains the bound: 2 + 2 + 2 = 2 · 3. Majority turns each 2/3 into a
    win, which gives the impossible value 3 out of 3. -/
theorem boole_attained :
    sup condorcetBallots 0 1 + sup condorcetBallots 1 2 + sup condorcetBallots 2 0 = 6 := by
  decide

/-! ### No deterministic rule is anonymous and neutral (three voters,
three alternatives) -/

/-- Rotate a list: the first voter becomes the last. -/
def rot {α : Type} : List α → List α
  | [] => []
  | x :: xs => xs ++ [x]

/-- The cyclic renaming a → b → c → a. -/
def cyc (x : Nat) : Nat := (x + 1) % 3

/-- The Condorcet profile, ballots listed best first. -/
def condorcetLists : List (List Nat) := [[0, 1, 2], [1, 2, 0], [2, 0, 1]]

/-- A rule returns one of the alternatives 0, 1, 2. It needs to be invariant
    only under rotating the voters (weaker than anonymity) and to commute only
    with the cyclic renaming (weaker than neutrality). Still impossible:
    the renaming carries the Condorcet profile to a rotation of itself, so the
    winner would be a fixed point of the renaming, and there is none. -/
theorem no_anonymous_neutral_rule (f : List (List Nat) → Nat)
    (valid : ∀ p, f p < 3)
    (anon : ∀ p, f (rot p) = f p)
    (neutral : ∀ p, f (p.map (·.map cyc)) = cyc (f p)) : False := by
  have e : condorcetLists.map (·.map cyc) = rot condorcetLists := by decide
  have h := neutral condorcetLists
  rw [e, anon] at h
  have hv := valid condorcetLists
  unfold cyc at h
  omega

end ProfileFacts
