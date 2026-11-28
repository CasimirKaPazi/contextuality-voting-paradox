/-
  The certificates of *Consistency as an Extension Problem*, Section 3d, for
  three alternatives and anonymous rules: the impossibility side of the
  thresholds of Section 3c for joins.

  Encoding. A profile counts the voters holding each of the six rankings
  abc, acb, bac, bca, cab, cba (`Prof`; anonymity is built in). `pref p x y`
  is the number of voters ranking x above y, and x is the Condorcet winner of
  p (`CW`) when it beats every other alternative by strict majority. A rule is
  given on all profiles, but every condition is asked only for electorates of
  at most N voters, so the theorems hold for rules on electorates up to N.

  * `det8`: no deterministic rule on electorates of up to eight voters elects
    the Condorcet winner (`CondDet`) and is consistent on joins (`ConsDet`:
    if two disjoint electorates elect the same alternative, so does their
    union). The proof is the note's case split on the Condorcet profile Q0:
    if W(Q0) = x, the join of Q0 with a five-voter electorate electing x
    forces the eight-voter profile above to x, while its two four-voter parts
    are pushed off x by their joins with Q0, and off the third alternative by
    a join with one voter, so both elect the alternative that beats x, and so
    does their union.
  * `lot9`: no lottery rule on electorates of up to nine voters gives the
    Condorcet winner probability 1 (`CondLot`) and satisfies the join
    inequality (J) of Section 3c (`ConsLot`), L(p + q)(a) ≥ L(p)(a) + L(q)(a)
    − 1. By Lemma 3 of *Four Levels* (`Couplings.lemma3`) this is the
    existence of joint draws on every join. The proof is the certificate of
    three rows around the doubled Condorcet profile.

  The single facts (Condorcet winners, sizes, sums of profiles) are checked by
  `decide`. Not here: the other side of the thresholds, that rules exist for
  fewer voters (seven for deterministic rules, eight for lotteries), and that
  the weakly compatible families at eight voters extend to empirical models.
  These rest on solutions found by linear and integer programming.
-/

module

public import Mathlib

@[expose] public section

namespace ConsistencyCertificates

/-- Positions of a, b, c in the rankings abc, acb, bac, bca, cab, cba. -/
def rk : Fin 6 → Fin 3 → ℕ :=
  ![![0, 1, 2], ![0, 2, 1], ![1, 0, 2], ![2, 0, 1], ![1, 2, 0], ![2, 1, 0]]

/-- An anonymous profile: the number of voters with each ranking. -/
abbrev Prof := Fin 6 → ℕ

def size (p : Prof) : ℕ := p 0 + p 1 + p 2 + p 3 + p 4 + p 5

/-- The number of voters ranking x above y. -/
def pref (p : Prof) (x y : Fin 3) : ℕ :=
  (if rk 0 x < rk 0 y then p 0 else 0) + (if rk 1 x < rk 1 y then p 1 else 0) +
    (if rk 2 x < rk 2 y then p 2 else 0) + (if rk 3 x < rk 3 y then p 3 else 0) +
    (if rk 4 x < rk 4 y then p 4 else 0) + (if rk 5 x < rk 5 y then p 5 else 0)

/-- x is the Condorcet winner of p. -/
def CW (p : Prof) (x : Fin 3) : Prop := ∀ y, y ≠ x → pref p y x < pref p x y

instance (p : Prof) (x : Fin 3) : Decidable (CW p x) := by
  unfold CW
  infer_instance

/-! ### Deterministic rules -/

/-- The Condorcet winner is elected, on electorates of up to N voters. -/
def CondDet (N : ℕ) (W : Prof → Fin 3) : Prop := ∀ p x, size p ≤ N → CW p x → W p = x

/-- Consistency on joins of non-empty electorates, with union of up to N voters. -/
def ConsDet (N : ℕ) (W : Prof → Fin 3) : Prop :=
  ∀ p q, 0 < size p → 0 < size q → size (p + q) ≤ N → W p = W q → W (p + q) = W p

/-- If q elects x and the union with p has another Condorcet winner, p does not
    elect x. -/
lemma excl {N : ℕ} {W : Prof → Fin 3} (hD : CondDet N W) (hC : ConsDet N W) {p q : Prof}
    {x y : Fin 3} (hp : 0 < size p) (hq : 0 < size q) (hs : size (p + q) ≤ N) (hqx : W q = x)
    (hu : CW (p + q) y) (hne : y ≠ x) : W p ≠ x := by
  intro hpx
  have h1 := hC p q hp hq hs (hpx.trans hqx.symm)
  have h2 := hD (p + q) y hs hu
  exact hne (h2.symm.trans (h1.trans hpx))

lemma ne01 : ∀ w : Fin 3, w ≠ 0 → w ≠ 1 → w = 2 := by decide
lemma ne12 : ∀ w : Fin 3, w ≠ 1 → w ≠ 2 → w = 0 := by decide
lemma ne02 : ∀ w : Fin 3, w ≠ 2 → w ≠ 0 → w = 1 := by decide

/-- The Condorcet profile and the nine profiles of the minimal unsatisfiable
    set (`scripts/consistency/yl_certificates.py`). -/
def Q0 : Prof := ![1, 0, 0, 1, 1, 0]
def Q1 : Prof := ![1, 1, 0, 0, 0, 2]
def Q2 : Prof := ![1, 0, 2, 0, 1, 0]
def Q3 : Prof := ![1, 0, 0, 1, 0, 2]
def Q4 : Prof := ![0, 2, 1, 1, 0, 0]
def Q5 : Prof := ![0, 2, 0, 1, 1, 0]
def Q6 : Prof := ![0, 0, 0, 2, 1, 1]
def Q7 : Prof := ![1, 3, 0, 1, 1, 2]
def Q8 : Prof := ![1, 2, 3, 1, 1, 0]
def Q9 : Prof := ![1, 0, 0, 3, 1, 3]

/-- **Deterministic rules, eight voters.** No anonymous Condorcet extension on
    electorates of up to eight voters is consistent on joins. -/
theorem det8 : ¬ ∃ W : Prof → Fin 3, CondDet 8 W ∧ ConsDet 8 W := by
  rintro ⟨W, hD, hC⟩
  have hcases : W Q0 = 0 ∨ W Q0 = 1 ∨ W Q0 = 2 := by
    generalize W Q0 = w
    fin_cases w <;> simp
  rcases hcases with h0 | h0 | h0
  · -- W Q0 = a
    have hX : W ![0, 3, 0, 0, 0, 2] = 0 := hD _ _ (by decide) (by decide)
    have htop : W Q7 = 0 := by
      rw [show Q7 = Q0 + ![0, 3, 0, 0, 0, 2] by decide,
        hC Q0 _ (by decide) (by decide) (by decide) (h0.trans hX.symm), h0]
    have Q1x : W Q1 ≠ 0 :=
      excl hD hC (q := Q0) (y := 2) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q1y : W Q1 ≠ 1 :=
      excl hD hC (q := ![0, 0, 0, 1, 0, 0]) (y := 2) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q1b : W Q1 = 2 := ne01 _ Q1x Q1y
    have Q5x : W Q5 ≠ 0 :=
      excl hD hC (q := Q0) (y := 2) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q5y : W Q5 ≠ 1 :=
      excl hD hC (q := ![0, 0, 0, 1, 0, 0]) (y := 2) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q5b : W Q5 = 2 := ne01 _ Q5x Q5y
    have hj := hC Q1 Q5 (by decide) (by decide) (by decide) (Q1b.trans Q5b.symm)
    rw [show Q1 + Q5 = Q7 by decide, htop, Q1b] at hj
    exact absurd hj (by decide)
  · -- W Q0 = b
    have hX : W ![0, 2, 3, 0, 0, 0] = 1 := hD _ _ (by decide) (by decide)
    have htop : W Q8 = 1 := by
      rw [show Q8 = Q0 + ![0, 2, 3, 0, 0, 0] by decide,
        hC Q0 _ (by decide) (by decide) (by decide) (h0.trans hX.symm), h0]
    have Q2x : W Q2 ≠ 1 :=
      excl hD hC (q := Q0) (y := 0) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q2y : W Q2 ≠ 2 :=
      excl hD hC (q := ![0, 0, 0, 0, 0, 1]) (y := 1) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q2b : W Q2 = 0 := ne12 _ Q2x Q2y
    have Q4x : W Q4 ≠ 1 :=
      excl hD hC (q := Q0) (y := 0) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q4y : W Q4 ≠ 2 :=
      excl hD hC (q := ![0, 0, 0, 0, 1, 0]) (y := 0) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q4b : W Q4 = 0 := ne12 _ Q4x Q4y
    have hj := hC Q2 Q4 (by decide) (by decide) (by decide) (Q2b.trans Q4b.symm)
    rw [show Q2 + Q4 = Q8 by decide, htop, Q2b] at hj
    exact absurd hj (by decide)
  · -- W Q0 = c
    have hX : W ![0, 0, 0, 2, 0, 3] = 2 := hD _ _ (by decide) (by decide)
    have htop : W Q9 = 2 := by
      rw [show Q9 = Q0 + ![0, 0, 0, 2, 0, 3] by decide,
        hC Q0 _ (by decide) (by decide) (by decide) (h0.trans hX.symm), h0]
    have Q3x : W Q3 ≠ 2 :=
      excl hD hC (q := Q0) (y := 1) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q3y : W Q3 ≠ 0 :=
      excl hD hC (q := ![0, 1, 0, 0, 0, 0]) (y := 2) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q3b : W Q3 = 1 := ne02 _ Q3x Q3y
    have Q6x : W Q6 ≠ 2 :=
      excl hD hC (q := Q0) (y := 1) (by decide) (by decide) (by decide) h0 (by decide) (by decide)
    have Q6y : W Q6 ≠ 0 :=
      excl hD hC (q := ![0, 1, 0, 0, 0, 0]) (y := 2) (by decide) (by decide) (by decide)
        (hD _ _ (by decide) (by decide)) (by decide) (by decide)
    have Q6b : W Q6 = 1 := ne02 _ Q6x Q6y
    have hj := hC Q3 Q6 (by decide) (by decide) (by decide) (Q3b.trans Q6b.symm)
    rw [show Q3 + Q6 = Q9 by decide, htop, Q3b] at hj
    exact absurd hj (by decide)

/-! ### Lotteries -/

/-- A lottery at every electorate of up to N voters. -/
def Lot (N : ℕ) (L : Prof → Fin 3 → ℝ) : Prop :=
  ∀ p, size p ≤ N → (∀ x, 0 ≤ L p x) ∧ L p 0 + L p 1 + L p 2 = 1

/-- The Condorcet winner gets probability 1. -/
def CondLot (N : ℕ) (L : Prof → Fin 3 → ℝ) : Prop := ∀ p x, size p ≤ N → CW p x → L p x = 1

/-- The join inequality (J) of Section 3c, for joins of up to N voters. -/
def ConsLot (N : ℕ) (L : Prof → Fin 3 → ℝ) : Prop :=
  ∀ p q, 0 < size p → 0 < size q → size (p + q) ≤ N → ∀ a, L p a + L q a - 1 ≤ L (p + q) a

/-- The doubled Condorcet profile and the three electorates of the certificate. -/
def q2 : Prof := ![2, 0, 0, 2, 2, 0]
def pa : Prof := ![0, 2, 0, 0, 1, 0]
def pb : Prof := ![1, 0, 2, 0, 0, 0]
def pc : Prof := ![0, 0, 1, 0, 0, 2]

/-- **Lotteries, nine voters.** No anonymous lottery rule on electorates of up
    to nine voters gives the Condorcet winner probability 1 and satisfies the
    join inequality. -/
theorem lot9 : ¬ ∃ L : Prof → Fin 3 → ℝ, Lot 9 L ∧ CondLot 9 L ∧ ConsLot 9 L := by
  rintro ⟨L, hL, hD, hJ⟩
  have ca : L pa 0 = 1 := hD _ _ (by decide) (by decide)
  have cb : L pb 1 = 1 := hD _ _ (by decide) (by decide)
  have cc : L pc 2 = 1 := hD _ _ (by decide) (by decide)
  have ua : L (pa + q2) 2 = 1 := hD _ _ (by decide) (by decide)
  have ub : L (pb + q2) 0 = 1 := hD _ _ (by decide) (by decide)
  have uc : L (pc + q2) 1 = 1 := hD _ _ (by decide) (by decide)
  obtain ⟨na, sa⟩ := hL (pa + q2) (by decide)
  obtain ⟨nb, sb⟩ := hL (pb + q2) (by decide)
  obtain ⟨nc, sc⟩ := hL (pc + q2) (by decide)
  have na1 := na 1
  have nb1 := nb 1
  have nb2 := nb 2
  have nc0 := nc 0
  have nc2 := nc 2
  have na0 := na 0
  have ja := hJ pa q2 (by decide) (by decide) (by decide) 0
  have jb := hJ pb q2 (by decide) (by decide) (by decide) 1
  have jc := hJ pc q2 (by decide) (by decide) (by decide) 2
  have sq := (hL q2 (by decide)).2
  linarith

end ConsistencyCertificates
