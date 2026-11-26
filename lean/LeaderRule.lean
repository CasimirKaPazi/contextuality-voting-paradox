/-
  The base case of *Strategic Information*
  (`notes/strategic-information/approval-plurality.md`): plurality and
  approval under one strategic rationale, a shared poll with leader `a1` and runner-up `a2`.

  The best replies are taken as definitions here: under plurality a voter
  votes for the preferred of `a1` and `a2`; under approval she follows the
  leader rule (approve `a1` exactly when `a1` is above `a2`, any other
  candidate exactly when it is above `a1`). That these are the best replies
  under the assumption (T) on ties is not formalised yet.

  Proved, for any finite list of voters and any type of candidates:
  * Proposition 1: the counts. Both front-runners have the same tally under
    both methods, every other candidate `x` has the approval tally N(x > a1)
    and no plurality votes; the plurality ballot is a function of the
    approval ballot and is contained in it.
  * Proposition 2: a poll confirms itself under approval exactly when `a1`
    beats every candidate by majority and `a2` is its unique strongest
    challenger; under plurality exactly when `a1` beats `a2` and some voter
    prefers `a2`; with a third candidate, every self-confirming approval poll
    confirms itself under plurality.
  * Proposition 3: the majority switch. A new leader of the approval tally
    beats the old leader by majority; a beaten leader that keeps the lead
    hands the runner-up position to a challenger who beats it, and loses the
    lead at the next poll; a Condorcet winner as leader keeps the lead.
  * The Smith set: a set of candidates each of whom beats every candidate
    outside it is never left once the leader is in it.
  * Proposition 4, the walk with memory, its steps: with the tally
    restricted to the eligible candidates (those that never led, and the
    current leader), a new leader beats the old one, a leader beaten by an
    eligible candidate falls at the next poll, a leader beating every eligible
    candidate keeps the lead, and a leader outside a dominant set whose
    members are all eligible is beaten by an eligible candidate. The counting
    that turns these steps into the bound 2(m − 1) is not formalised yet.

  Uses only core Lean, no Mathlib. A ballot is a function giving each
  candidate a position (smaller is better); preferences are strict.
-/

module

@[expose] public section

namespace LeaderRule

variable {V A : Type}

/-! ### Counting -/

/-- Number of voters in the list for which `P` holds. -/
def countIf (P : V → Bool) : List V → Nat
  | [] => 0
  | i :: vs =>
    match P i with
    | true => countIf P vs + 1
    | false => countIf P vs

theorem countIf_congr {P Q : V → Bool} (h : ∀ i, P i = Q i) (vs : List V) :
    countIf P vs = countIf Q vs := by
  have hPQ : P = Q := funext h
  rw [hPQ]

theorem countIf_eq_zero {P : V → Bool} (h : ∀ i, P i = false) :
    ∀ vs : List V, countIf P vs = 0
  | [] => rfl
  | i :: vs => by
    have ih := countIf_eq_zero h vs
    simp only [countIf, h i, ih]

/-- A predicate and its negation count every voter once. -/
theorem countIf_add_compl {P Q : V → Bool} (h : ∀ i, Q i = !P i) :
    ∀ vs : List V, countIf P vs + countIf Q vs = vs.length
  | [] => rfl
  | i :: vs => by
    have ih := countIf_add_compl h vs
    cases hp : P i with
    | true =>
      have hq : Q i = false := by simp [h i, hp]
      simp only [countIf, hp, hq, List.length_cons]
      omega
    | false =>
      have hq : Q i = true := by simp [h i, hp]
      simp only [countIf, hp, hq, List.length_cons]
      omega

/-! ### Profiles and majorities -/

/-- Preferences are strict: no voter puts two candidates in one position. -/
def Strict (p : V → A → Nat) : Prop := ∀ i x y, x ≠ y → p i x ≠ p i y

/-- N(x > y): the number of voters ranking `x` above `y`. -/
def pref (p : V → A → Nat) (vs : List V) (x y : A) : Nat :=
  countIf (fun i => decide (p i x < p i y)) vs

/-- `x` beats `y` by majority. -/
def beats (p : V → A → Nat) (vs : List V) (x y : A) : Prop :=
  pref p vs y x < pref p vs x y

theorem pref_add (p : V → A → Nat) (hs : Strict p) (vs : List V) {x y : A}
    (hxy : x ≠ y) : pref p vs x y + pref p vs y x = vs.length := by
  unfold pref
  apply countIf_add_compl
  intro i
  have hne := hs i x y hxy
  by_cases h : p i x < p i y
  · have h' : ¬ p i y < p i x := by omega
    simp [h, h']
  · have h' : p i y < p i x := by omega
    simp [h, h']

/-! ### The two best replies -/

variable [DecidableEq A]

/-- The leader rule: the approval ballot of voter `i` at the poll `(a1, a2)`. -/
def approve (p : V → A → Nat) (a1 a2 : A) (i : V) (x : A) : Bool :=
  if x = a1 then decide (p i a1 < p i a2) else decide (p i x < p i a1)

/-- The approval tally at the poll `(a1, a2)`. -/
def tally (p : V → A → Nat) (vs : List V) (a1 a2 x : A) : Nat :=
  countIf (fun i => approve p a1 a2 i x) vs

/-- The plurality vote of voter `i` at the poll `(a1, a2)`. -/
def pvote (p : V → A → Nat) (a1 a2 : A) (i : V) : A :=
  if p i a1 < p i a2 then a1 else a2

/-- The plurality tally at the poll `(a1, a2)`. -/
def ptally (p : V → A → Nat) (vs : List V) (a1 a2 x : A) : Nat :=
  countIf (fun i => decide (pvote p a1 a2 i = x)) vs

/-! ### Proposition 1: what the ballots carry -/

theorem tally_leader (p : V → A → Nat) (vs : List V) (a1 a2 : A) :
    tally p vs a1 a2 a1 = pref p vs a1 a2 := by
  unfold tally pref
  apply countIf_congr
  intro i
  simp [approve]

theorem tally_other (p : V → A → Nat) (vs : List V) (a1 a2 : A) {x : A}
    (hx : x ≠ a1) : tally p vs a1 a2 x = pref p vs x a1 := by
  unfold tally pref
  apply countIf_congr
  intro i
  simp [approve, hx]

theorem ptally_leader (p : V → A → Nat) (vs : List V) {a1 a2 : A} (h12 : a1 ≠ a2) :
    ptally p vs a1 a2 a1 = pref p vs a1 a2 := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  unfold ptally pref
  apply countIf_congr
  intro i
  by_cases h : p i a1 < p i a2
  · simp [pvote, h]
  · simp [pvote, h, h21]

theorem ptally_runner (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 : A}
    (h12 : a1 ≠ a2) : ptally p vs a1 a2 a2 = pref p vs a2 a1 := by
  unfold ptally pref
  apply countIf_congr
  intro i
  have hne := hs i a1 a2 h12
  by_cases h : p i a1 < p i a2
  · have h' : ¬ p i a2 < p i a1 := by omega
    simp [pvote, h, h', h12]
  · have h' : p i a2 < p i a1 := by omega
    simp [pvote, h, h']

theorem ptally_other (p : V → A → Nat) (vs : List V) {a1 a2 x : A}
    (hx1 : x ≠ a1) (hx2 : x ≠ a2) : ptally p vs a1 a2 x = 0 := by
  have h1 : a1 ≠ x := fun h => hx1 h.symm
  have h2 : a2 ≠ x := fun h => hx2 h.symm
  unfold ptally
  apply countIf_eq_zero
  intro i
  by_cases h : p i a1 < p i a2
  · simp [pvote, h, h1]
  · simp [pvote, h, h2]

/-- The plurality ballot is a function of the approval ballot. -/
theorem pvote_of_approve (p : V → A → Nat) (a1 a2 : A) (i : V) :
    pvote p a1 a2 i = if approve p a1 a2 i a1 = true then a1 else a2 := by
  by_cases h : p i a1 < p i a2
  · simp [pvote, approve, h]
  · simp [pvote, approve, h]

/-- The plurality ballot lies inside the approval ballot. -/
theorem approve_pvote (p : V → A → Nat) (hs : Strict p) {a1 a2 : A} (h12 : a1 ≠ a2)
    (i : V) : approve p a1 a2 i (pvote p a1 a2 i) = true := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  have hne := hs i a1 a2 h12
  by_cases h : p i a1 < p i a2
  · simp [pvote, approve, h]
  · have h' : p i a2 < p i a1 := by omega
    simp [pvote, approve, h, h21, h']

/-! ### Proposition 2: self-confirming polls -/

/-- The approval tally at the poll ranks `a1` first and `a2` second, strictly. -/
def SelfConfirming (p : V → A → Nat) (vs : List V) (a1 a2 : A) : Prop :=
  tally p vs a1 a2 a2 < tally p vs a1 a2 a1 ∧
    ∀ x, x ≠ a1 → x ≠ a2 → tally p vs a1 a2 x < tally p vs a1 a2 a2

/-- The plurality tally at the poll ranks `a1` first and `a2` second, strictly. -/
def PSelfConfirming (p : V → A → Nat) (vs : List V) (a1 a2 : A) : Prop :=
  ptally p vs a1 a2 a2 < ptally p vs a1 a2 a1 ∧
    ∀ x, x ≠ a1 → x ≠ a2 → ptally p vs a1 a2 x < ptally p vs a1 a2 a2

theorem selfConfirming_iff (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 : A}
    (h12 : a1 ≠ a2) :
    SelfConfirming p vs a1 a2 ↔
      (∀ y, y ≠ a1 → beats p vs a1 y) ∧
        ∀ x, x ≠ a1 → x ≠ a2 → pref p vs x a1 < pref p vs a2 a1 := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  unfold SelfConfirming beats
  rw [tally_leader, tally_other p vs a1 a2 h21]
  have hsum := pref_add p hs vs h12
  constructor
  · rintro ⟨h1, h2⟩
    have hx : ∀ x, x ≠ a1 → x ≠ a2 → pref p vs x a1 < pref p vs a2 a1 := by
      intro x hx1 hx2
      have := h2 x hx1 hx2
      rwa [tally_other p vs a1 a2 hx1] at this
    refine ⟨?_, hx⟩
    intro y hy
    by_cases hy2 : y = a2
    · subst hy2; exact h1
    · have hlt := hx y hy hy2
      have hsy := pref_add p hs vs hy
      omega
  · rintro ⟨h1, h2⟩
    refine ⟨h1 a2 h21, ?_⟩
    intro x hx1 hx2
    rw [tally_other p vs a1 a2 hx1]
    exact h2 x hx1 hx2

theorem pSelfConfirming_iff (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 : A}
    (h12 : a1 ≠ a2) (hthird : ∃ x, x ≠ a1 ∧ x ≠ a2) :
    PSelfConfirming p vs a1 a2 ↔ beats p vs a1 a2 ∧ 0 < pref p vs a2 a1 := by
  unfold PSelfConfirming beats
  rw [ptally_leader p vs h12, ptally_runner p hs vs h12]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨x, hx1, hx2⟩ := hthird
    have := h2 x hx1 hx2
    rw [ptally_other p vs hx1 hx2] at this
    exact ⟨h1, this⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    intro x hx1 hx2
    rw [ptally_other p vs hx1 hx2]
    exact h2

/-- Every self-confirming approval poll confirms itself under plurality. -/
theorem selfConfirming_plurality (p : V → A → Nat) (hs : Strict p) (vs : List V)
    {a1 a2 : A} (h12 : a1 ≠ a2) (hthird : ∃ x, x ≠ a1 ∧ x ≠ a2)
    (h : SelfConfirming p vs a1 a2) : PSelfConfirming p vs a1 a2 := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  rw [pSelfConfirming_iff p hs vs h12 hthird]
  obtain ⟨hw, hc⟩ := (selfConfirming_iff p hs vs h12).1 h
  obtain ⟨x, hx1, hx2⟩ := hthird
  exact ⟨hw a2 h21, Nat.lt_of_le_of_lt (Nat.zero_le _) (hc x hx1 hx2)⟩

/-! ### Proposition 3: the majority switch -/

/-- `L` leads the approval tally at the poll `(a1, a2)` strictly. -/
def Leads (p : V → A → Nat) (vs : List V) (a1 a2 L : A) : Prop :=
  ∀ y, y ≠ L → tally p vs a1 a2 y < tally p vs a1 a2 L

/-- `c` is strictly second in the approval tally, behind `a1`. -/
def Second (p : V → A → Nat) (vs : List V) (a1 a2 c : A) : Prop :=
  ∀ y, y ≠ a1 → y ≠ c → tally p vs a1 a2 y < tally p vs a1 a2 c

/-- Part 1: a new leader beats the old leader by majority. -/
theorem new_leader_beats (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 L : A}
    (h12 : a1 ≠ a2) (hL1 : L ≠ a1) (hL : Leads p vs a1 a2 L) : beats p vs L a1 := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  unfold beats
  have hsum := pref_add p hs vs h12
  have hsL := pref_add p hs vs hL1
  have ha1 := hL a1 (fun h => hL1 h.symm)
  rw [tally_leader, tally_other p vs a1 a2 hL1] at ha1
  by_cases hL2 : L = a2
  · subst hL2
    omega
  · have ha2 := hL a2 (fun h => hL2 h.symm)
    rw [tally_other p vs a1 a2 h21, tally_other p vs a1 a2 hL1] at ha2
    omega

/-- Part 2: if `a1` is beaten by some candidate and keeps the lead, the new
    runner-up `c` beats `a1`, and at the poll `(a1, c)` the tally of `c`
    exceeds that of `a1`. -/
theorem beaten_leader_falls (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 c : A}
    (hc1 : c ≠ a1) (hsec : Second p vs a1 a2 c) (hbeaten : ∃ b, b ≠ a1 ∧ beats p vs b a1) :
    beats p vs c a1 ∧ tally p vs a1 c a1 < tally p vs a1 c c := by
  obtain ⟨b, hb1, hb⟩ := hbeaten
  unfold beats at hb
  have hsb := pref_add p hs vs hb1
  have hsc := pref_add p hs vs hc1
  have hcb : pref p vs b a1 ≤ pref p vs c a1 := by
    by_cases hbc : b = c
    · subst hbc; exact Nat.le_refl _
    · have := hsec b hb1 hbc
      rw [tally_other p vs a1 a2 hb1, tally_other p vs a1 a2 hc1] at this
      exact Nat.le_of_lt this
  have hwin : beats p vs c a1 := by
    unfold beats
    omega
  refine ⟨hwin, ?_⟩
  rw [tally_leader, tally_other p vs a1 c hc1]
  exact hwin

/-- Part 3: a Condorcet winner as leader keeps the lead. -/
theorem condorcet_keeps (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 : A}
    (h12 : a1 ≠ a2) (hcw : ∀ y, y ≠ a1 → beats p vs a1 y) : Leads p vs a1 a2 a1 := by
  intro y hy
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  have hw2 := hcw a2 h21
  have hwy := hcw y hy
  unfold beats at hw2 hwy
  have hs2 := pref_add p hs vs h12
  have hy' : a1 ≠ y := fun h => hy h.symm
  have hsy := pref_add p hs vs hy'
  rw [tally_leader, tally_other p vs a1 a2 hy]
  omega

/-! ### The Smith set is never left -/

/-- `S` dominates: each of its members beats every candidate outside it. -/
def Dominant (p : V → A → Nat) (vs : List V) (S : A → Prop) : Prop :=
  ∀ x y, S x → ¬ S y → beats p vs x y

/-- A new leader of the approval tally stays in a dominant set that contains
    the old leader. -/
theorem stays_dominant (p : V → A → Nat) (hs : Strict p) (vs : List V) {a1 a2 L : A}
    {S : A → Prop} (hS : Dominant p vs S) (h12 : a1 ≠ a2) (hL1 : L ≠ a1)
    (hL : Leads p vs a1 a2 L) (ha1 : S a1) : S L := by
  have hb := new_leader_beats p hs vs h12 hL1 hL
  refine Classical.byContradiction (fun hSL => ?_)
  have hb' := hS a1 L ha1 hSL
  unfold beats at hb hb'
  omega

/-! ### Proposition 4: the steps of the walk with memory -/

/-- `L` leads the approval tally among the eligible candidates `E`. -/
def LeadsIn (p : V → A → Nat) (vs : List V) (E : A → Prop) (a1 a2 L : A) : Prop :=
  ∀ y, E y → y ≠ L → tally p vs a1 a2 y < tally p vs a1 a2 L

/-- `c` is strictly second among the eligible candidates, behind `a1`. -/
def SecondIn (p : V → A → Nat) (vs : List V) (E : A → Prop) (a1 a2 c : A) : Prop :=
  ∀ y, E y → y ≠ a1 → y ≠ c → tally p vs a1 a2 y < tally p vs a1 a2 c

/-- Step 1: with an eligible leader and runner-up, a new leader among the
    eligible candidates beats the old leader by majority. -/
theorem new_leader_beats_in (p : V → A → Nat) (hs : Strict p) (vs : List V)
    {E : A → Prop} {a1 a2 L : A} (h12 : a1 ≠ a2) (hE1 : E a1) (hE2 : E a2)
    (hL1 : L ≠ a1) (hL : LeadsIn p vs E a1 a2 L) : beats p vs L a1 := by
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  unfold beats
  have hsum := pref_add p hs vs h12
  have hsL := pref_add p hs vs hL1
  have ha1 := hL a1 hE1 (fun h => hL1 h.symm)
  rw [tally_leader, tally_other p vs a1 a2 hL1] at ha1
  by_cases hL2 : L = a2
  · subst hL2
    omega
  · have ha2 := hL a2 hE2 (fun h => hL2 h.symm)
    rw [tally_other p vs a1 a2 h21, tally_other p vs a1 a2 hL1] at ha2
    omega

/-- Step 2: if an eligible candidate beats `a1` and `a1` keeps the lead, the
    eligible runner-up `c` beats `a1` and wins the tally at the poll `(a1, c)`. -/
theorem beaten_leader_falls_in (p : V → A → Nat) (hs : Strict p) (vs : List V)
    {E : A → Prop} {a1 a2 c : A} (hc1 : c ≠ a1) (hsec : SecondIn p vs E a1 a2 c)
    (hbeaten : ∃ b, E b ∧ b ≠ a1 ∧ beats p vs b a1) :
    beats p vs c a1 ∧ tally p vs a1 c a1 < tally p vs a1 c c := by
  obtain ⟨b, hEb, hb1, hb⟩ := hbeaten
  unfold beats at hb
  have hsb := pref_add p hs vs hb1
  have hsc := pref_add p hs vs hc1
  have hcb : pref p vs b a1 ≤ pref p vs c a1 := by
    by_cases hbc : b = c
    · subst hbc; exact Nat.le_refl _
    · have := hsec b hEb hb1 hbc
      rw [tally_other p vs a1 a2 hb1, tally_other p vs a1 a2 hc1] at this
      exact Nat.le_of_lt this
  have hwin : beats p vs c a1 := by
    unfold beats
    omega
  refine ⟨hwin, ?_⟩
  rw [tally_leader, tally_other p vs a1 c hc1]
  exact hwin

/-- Step 3: a leader who beats every eligible candidate, with an eligible
    runner-up, leads the eligible tally. -/
theorem keeps_in (p : V → A → Nat) (hs : Strict p) (vs : List V) {E : A → Prop}
    {a1 a2 : A} (h12 : a1 ≠ a2) (hE2 : E a2)
    (hw : ∀ y, E y → y ≠ a1 → beats p vs a1 y) : LeadsIn p vs E a1 a2 a1 := by
  intro y hEy hy
  have h21 : a2 ≠ a1 := fun h => h12 h.symm
  have hw2 := hw a2 hE2 h21
  have hwy := hw y hEy hy
  unfold beats at hw2 hwy
  have hs2 := pref_add p hs vs h12
  have hy' : a1 ≠ y := fun h => hy h.symm
  have hsy := pref_add p hs vs hy'
  rw [tally_leader, tally_other p vs a1 a2 hy]
  omega

omit [DecidableEq A] in
/-- Step 4: a leader outside a dominant set, all of whose members are
    eligible, is beaten by an eligible candidate. -/
theorem dominant_challenger (p : V → A → Nat) (vs : List V) {E S : A → Prop} {L s : A}
    (hS : Dominant p vs S) (hL : ¬ S L) (hs : S s) (hE : ∀ x, S x → E x) :
    E s ∧ s ≠ L ∧ beats p vs s L := by
  refine ⟨hE s hs, ?_, hS s L hs hL⟩
  intro h
  exact hL (h ▸ hs)

end LeaderRule
