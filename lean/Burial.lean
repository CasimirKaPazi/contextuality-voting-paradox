/-
  Proposition 1 of *Walls and Strategy* (burial): if x beats z by
  majority, voters who already rank z above x cannot change that by changing
  their ballots. Any number of voters and alternatives.
  Uses only core Lean, no Mathlib.

  A ballot is a function giving each alternative a position (smaller is
  better). Positions may coincide, so the statement also holds for ballots
  with ties.
-/

module

@[expose] public section

namespace Burial

variable {V A : Type}

/-- Number of voters in the list for which `P` holds. -/
def countIf (P : V → Bool) : List V → Nat
  | [] => 0
  | i :: vs =>
    match P i with
    | true => countIf P vs + 1
    | false => countIf P vs

/-- If `P` implies `Q` for every voter, fewer voters satisfy `P` than `Q`. -/
theorem countIf_mono (P Q : V → Bool) (h : ∀ i, P i = true → Q i = true) :
    ∀ vs : List V, countIf P vs ≤ countIf Q vs
  | [] => Nat.le_refl 0
  | i :: vs => by
    have ih := countIf_mono P Q h vs
    cases hp : P i with
    | true =>
      have hq : Q i = true := h i hp
      simp only [countIf, hp, hq]
      omega
    | false =>
      cases hq : Q i with
      | true =>
        simp only [countIf, hp, hq]
        omega
      | false =>
        simp only [countIf, hp, hq]
        omega

/-- Ballot `r` ranks x strictly above y. -/
def prefers (r : A → Nat) (x y : A) : Bool := decide (r x < r y)

/-- Number of voters ranking x strictly above y. -/
def support (p : V → A → Nat) (vs : List V) (x y : A) : Nat :=
  countIf (fun i => prefers (p i) x y) vs

/-- Burial. In profile `p`, x beats z. The voters marked by `inS` all rank
    z above x; they may change their ballots arbitrarily (profile `p'`), the
    others keep theirs. Then x still beats z in `p'`, so z is not a Condorcet
    winner of `p'`. -/
theorem burial (p p' : V → A → Nat) (vs : List V) (inS : V → Bool) (x z : A)
    (hS : ∀ i, inS i = true → prefers (p i) z x = true)
    (hOut : ∀ i, inS i = false → p' i = p i)
    (hx : support p vs z x < support p vs x z) :
    support p' vs z x < support p' vs x z := by
  -- No voter newly ranks z above x.
  have h1 : support p' vs z x ≤ support p vs z x := by
    unfold support
    apply countIf_mono
    intro i hi
    have hi' : prefers (p' i) z x = true := hi
    show prefers (p i) z x = true
    cases hs : inS i with
    | true => exact hS i hs
    | false =>
      rw [hOut i hs] at hi'
      exact hi'
  -- No voter stops ranking x above z.
  have h2 : support p vs x z ≤ support p' vs x z := by
    unfold support
    apply countIf_mono
    intro i hi
    have hi' : prefers (p i) x z = true := hi
    show prefers (p' i) x z = true
    cases hs : inS i with
    | true =>
      have hz := hS i hs
      simp only [prefers, decide_eq_true_eq] at hi' hz
      omega
    | false =>
      rw [hOut i hs]
      exact hi'
  omega

end Burial
