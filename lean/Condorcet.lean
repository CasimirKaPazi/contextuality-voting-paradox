/-
  Finite facts about three voters and three alternatives, checked by
  computation inside the proof assistant (`decide`).
  Uses only core Lean, no Mathlib.
-/

module

@[expose] public section

namespace Condorcet

inductive Alt where
  | a | b | c
  deriving DecidableEq, Repr

/-- A strict ranking, given as the position of each alternative (0 = best). -/
abbrev Ranking := Alt → Nat

def abc : Ranking | .a => 0 | .b => 1 | .c => 2
def acb : Ranking | .a => 0 | .c => 1 | .b => 2
def bac : Ranking | .b => 0 | .a => 1 | .c => 2
def bca : Ranking | .b => 0 | .c => 1 | .a => 2
def cab : Ranking | .c => 0 | .a => 1 | .b => 2
def cba : Ranking | .c => 0 | .b => 1 | .a => 2

/-- All six strict rankings of three alternatives. -/
def rankings : List Ranking := [abc, acb, bac, bca, cab, cba]

/-- A profile: one ranking per voter. -/
abbrev Profile := List Ranking

/-- Number of voters who rank `x` above `y`. -/
def support (p : Profile) (x y : Alt) : Nat :=
  (p.filter (fun r => decide (r x < r y))).length

/-- A majority prefers `x` to `y`. -/
def maj (p : Profile) (x y : Alt) : Bool :=
  decide (support p y x < support p x y)

/-- The classic Condorcet profile. -/
def condorcetProfile : Profile := [abc, bca, cab]

/-- Majority goes a > b > c > a. -/
theorem condorcet_cycle :
    maj condorcetProfile .a .b = true ∧
    maj condorcetProfile .b .c = true ∧
    maj condorcetProfile .c .a = true := by
  decide

/-- Every alternative loses to some other one: there is no Condorcet winner. -/
theorem no_condorcet_winner : ∀ x : Alt, ∃ y, maj condorcetProfile y x = true := by
  intro x
  cases x
  · exact ⟨.c, by decide⟩
  · exact ⟨.a, by decide⟩
  · exact ⟨.b, by decide⟩

def alts : List Alt := [.a, .b, .c]

/-- Some alternative beats every other one by majority. -/
def hasWinner (p : Profile) : Bool :=
  alts.any fun x => alts.all fun y => x == y || maj p x y

/-- The majority relation is one of the two 3-cycles. -/
def isCycle (p : Profile) : Bool :=
  (maj p .a .b && maj p .b .c && maj p .c .a) ||
  (maj p .b .a && maj p .c .b && maj p .a .c)

/-- For all 6³ = 216 profiles of three voters: either there is a Condorcet
    winner or the majority relation is a full cycle. Nothing in between. -/
theorem winner_or_cycle :
    (rankings.all fun r1 => rankings.all fun r2 => rankings.all fun r3 =>
      hasWinner [r1, r2, r3] || isCycle [r1, r2, r3]) = true := by
  decide

/-- Number of the 216 profiles whose majority relation is a cycle. -/
def countCycles : Nat :=
  rankings.foldl (fun acc1 r1 =>
    rankings.foldl (fun acc2 r2 =>
      rankings.foldl (fun acc3 r3 =>
        if isCycle [r1, r2, r3] then acc3 + 1 else acc3) acc2) acc1) 0

set_option maxRecDepth 100000 in
/-- Exactly 12 of 216 profiles are Condorcet paradoxes: the known
    probability 1/18 under uniformly random rankings. -/
theorem count_cycles : countCycles = 12 := by
  decide

end Condorcet
