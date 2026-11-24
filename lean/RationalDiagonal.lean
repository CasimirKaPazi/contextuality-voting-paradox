/-
  Proposition 4 of *Walls and Strategy* (rational diagonal), checked by
  certificates, and the veto-then-pick example of its Section 3 (simultaneity).
  Uses only core Lean, no Mathlib.

  A game form *admits a rational diagonal* for voter 1 if there are strict
  preferences P for voter 1 and Q for the others such that for every ballot b
  of voter 1 there is a profile c of the others' ballots with
  (1) every other voter best-responding in (b, c) under its preference, and
  (2) b not a best reply for voter 1 against c under P.

  The search for P, Q and the table b ↦ c was done in Python. Lean only checks
  the tables: each theorem below says that one explicit table satisfies (1)
  and (2) for all six ballots b. This is the certificate method: finding a
  witness may be expensive, checking it is cheap.

  The 18,138 two-player game forms of Proposition 4 are not included: the
  certificates would be easy, but proving that the list of game forms is
  complete would need its own enumeration argument.
-/

module

@[expose] public section

set_option maxRecDepth 100000

namespace RationalDiagonal

/-- Alternatives are 0 = a, 1 = b, 2 = c. A ranking lists them best first. -/
abbrev Ranking := List Nat
abbrev Profile := List Ranking

def rankings : List Ranking :=
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]]

/-- Position of x in a ranking (0 = top). -/
def pos : Ranking → Nat → Nat
  | [], _ => 0
  | y :: ys, x => if y == x then 0 else pos ys x + 1

def sumOver (p : Profile) (f : Ranking → Nat) : Nat :=
  p.foldl (fun acc r => acc + f r) 0

/-- Highest score wins; ties go to the earlier letter. -/
def argmaxTB (s : Nat → Nat) : Nat :=
  [1, 2].foldl (fun best y => if s best < s y then y else best) 0

def isTop (x : Nat) : Ranking → Nat
  | y :: _ => if y == x then 1 else 0
  | [] => 0

def plurality (p : Profile) : Nat :=
  argmaxTB fun x => sumOver p (isTop x)

def borda (p : Profile) : Nat :=
  argmaxTB fun x => sumOver p (fun r => 2 - pos r x)

/-- First alternative of the ranking that is still in the race. -/
def topAlive (alive : List Nat) : Ranking → Nat
  | [] => 0
  | y :: ys => if alive.contains y then y else topAlive alive ys

/-- Fewest first preferences among the alive alternatives is eliminated;
    among ties, the later letter. -/
def loser (p : Profile) (alive : List Nat) : Nat :=
  let s := fun x => sumOver p (fun r => if topAlive alive r == x then 1 else 0)
  match alive with
  | [] => 0
  | a :: rest => rest.foldl (fun l y => if decide (s y < s l) || (s y == s l && decide (l < y)) then y else l) a

/-- Instant runoff with three alternatives: two elimination rounds. -/
def irv (p : Profile) : Nat :=
  let a1 := [0, 1, 2].filter (· != loser p [0, 1, 2])
  let a2 := a1.filter (· != loser p a1)
  a2.headD 0

/-- x beats every other alternative by a strict majority. -/
def beatsAll (p : Profile) (x : Nat) : Bool :=
  [0, 1, 2].all fun y =>
    y == x || decide (p.length < 2 * sumOver p (fun r => if pos r x < pos r y then 1 else 0))

/-- Black's rule: the Condorcet winner if there is one, otherwise Borda. -/
def black (p : Profile) : Nat :=
  match [0, 1, 2].find? (beatsAll p) with
  | some x => x
  | none => borda p

def util (pref : Ranking) (x : Nat) : Nat := 2 - pos pref x

/-- Voter k's ballot in profile p is a best reply under preference `pref`. -/
def isBR (rule : Profile → Nat) (p : Profile) (k : Nat) (pref : Ranking) : Bool :=
  rankings.all fun bb => decide (util pref (rule (p.set k bb)) ≤ util pref (rule p))

/-- The certificate check. `table` lists, for each of the six ballots b of
    voter 1 (in the order of `rankings`), the ballots c of the other voters.
    Checks that all ballots and preferences are rankings, that every other
    voter best-responds in (b, c), and that b is not a best reply for
    voter 1. -/
def certOK (rule : Profile → Nat) (P : Ranking) (Qs : List Ranking)
    (table : List (List Ranking)) : Bool :=
  rankings.contains P && Qs.all (fun q => rankings.contains q) &&
  table.length == 6 &&
  (rankings.zip table).all fun bc =>
    let prof := bc.1 :: bc.2
    bc.2.length == Qs.length && bc.2.all (fun r => rankings.contains r) &&
    ((List.range Qs.length).all fun j => isBR rule prof (j + 1) (Qs.getD j [])) &&
    !isBR rule prof 0 P

/-- plurality, 2 voters: voter 1 with preference [2, 0, 1], others [1, 0, 2]. -/
theorem plurality_2_voters :
    certOK plurality [2, 0, 1] [[1, 0, 2]]
    [[[2, 0, 1]],
     [[2, 0, 1]],
     [[1, 0, 2]],
     [[1, 0, 2]],
     [[1, 0, 2]],
     [[1, 0, 2]]] = true := by
  decide +kernel

/-- plurality, 3 voters: voter 1 with preference [1, 2, 0], others [0, 1, 2], [0, 1, 2]. -/
theorem plurality_3_voters :
    certOK plurality [1, 2, 0] [[0, 1, 2], [0, 1, 2]]
    [[[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [2, 0, 1]],
     [[0, 1, 2], [2, 0, 1]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [1, 0, 2]]] = true := by
  decide +kernel

/-- Borda, 2 voters: voter 1 with preference [0, 1, 2], others [1, 2, 0]. -/
theorem borda_2_voters :
    certOK borda [0, 1, 2] [[1, 2, 0]]
    [[[1, 2, 0]],
     [[2, 1, 0]],
     [[1, 0, 2]],
     [[0, 1, 2]],
     [[1, 2, 0]],
     [[1, 0, 2]]] = true := by
  decide +kernel

/-- Borda, 3 voters: voter 1 with preference [0, 1, 2], others [1, 2, 0], [1, 2, 0]. -/
theorem borda_3_voters :
    certOK borda [0, 1, 2] [[1, 2, 0], [1, 2, 0]]
    [[[1, 0, 2], [1, 0, 2]],
     [[2, 0, 1], [2, 0, 1]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [2, 1, 0]],
     [[0, 1, 2], [1, 0, 2]]] = true := by
  decide +kernel

/-- IRV, 2 voters: voter 1 with preference [2, 0, 1], others [1, 0, 2]. -/
theorem irv_2_voters :
    certOK irv [2, 0, 1] [[1, 0, 2]]
    [[[2, 0, 1]],
     [[2, 0, 1]],
     [[1, 0, 2]],
     [[1, 0, 2]],
     [[1, 0, 2]],
     [[1, 0, 2]]] = true := by
  decide +kernel

/-- IRV, 3 voters: voter 1 with preference [0, 2, 1], others [1, 0, 2], [1, 2, 0]. -/
theorem irv_3_voters :
    certOK irv [0, 2, 1] [[1, 0, 2], [1, 2, 0]]
    [[[1, 0, 2], [2, 1, 0]],
     [[1, 0, 2], [2, 1, 0]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [2, 0, 1]],
     [[0, 1, 2], [1, 0, 2]]] = true := by
  decide +kernel

/-- Black, 2 voters: voter 1 with preference [0, 1, 2], others [1, 2, 0]. -/
theorem black_2_voters :
    certOK black [0, 1, 2] [[1, 2, 0]]
    [[[1, 2, 0]],
     [[2, 1, 0]],
     [[1, 0, 2]],
     [[0, 1, 2]],
     [[1, 2, 0]],
     [[1, 0, 2]]] = true := by
  decide +kernel

/-- Black, 3 voters: voter 1 with preference [0, 1, 2], others [1, 2, 0], [2, 1, 0]. -/
theorem black_3_voters :
    certOK black [0, 1, 2] [[1, 2, 0], [2, 1, 0]]
    [[[1, 0, 2], [2, 1, 0]],
     [[1, 2, 0], [2, 0, 1]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [1, 0, 2]],
     [[0, 1, 2], [2, 0, 1]],
     [[0, 1, 2], [2, 0, 1]]] = true := by
  decide +kernel

/-! ### Veto, then pick

Voter 1 vetoes one of a, b, c; voter 2 sees the veto and picks one of the
remaining two. In normal form voter 2 has 8 plans (a choice for each veto). -/

/-- The outcome when voter 1 vetoes `v` and voter 2 follows `plan`. -/
def outcome (v : Nat) (plan : List Nat) : Nat :=
  ([0, 1, 2].filter (· != v)).getD (plan.getD v 0) 0

def plans : List (List Nat) :=
  [[0,0,0],[0,0,1],[0,1,0],[0,1,1],[1,0,0],[1,0,1],[1,1,0],[1,1,1]]

def br1 (plan : List Nat) (P : Ranking) (v : Nat) : Bool :=
  [0, 1, 2].all fun v' => decide (util P (outcome v' plan) ≤ util P (outcome v plan))

def br2 (v : Nat) (Q : Ranking) (plan : List Nat) : Bool :=
  plans.all fun pl => decide (util Q (outcome v pl) ≤ util Q (outcome v plan))

/-- Rational diagonal for voter 1 when voter 2 need only best-respond in the
    normal form: every veto v is answered by some best-reply plan of voter 2
    against which v is not a best reply. -/
def nashDiagonal (P Q : Ranking) : Bool :=
  [0, 1, 2].all fun v => plans.any fun t => br2 v Q t && !br1 t P v

def nashCount : Nat :=
  rankings.foldl (fun acc P =>
    rankings.foldl (fun acc2 Q => if nashDiagonal P Q then acc2 + 1 else acc2) acc) 0

/-- The diagonal works in 12 of the 36 pairs of strict preferences. With
    sequential rationality voter 2's plan is fixed by its preference, and voter 1
    simply best-responds to that plan, so no diagonal is possible. -/
theorem veto_then_pick : nashCount = 12 := by
  decide +kernel

end RationalDiagonal
