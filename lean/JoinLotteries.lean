module

public import Mathlib

@[expose] public section

/-!
# Lotteries on joins: Lemma 3 (necessity) and Theorem 4 of *Four Levels*

* **Lemma 3, necessary direction** (`lemma3_nec`). If winners `X ~ μ`, `Y ~ ν`, `Z ~ λ` can be
  drawn jointly so that `X = Y` implies `Z = X`, then `λ a ≥ μ a + ν a − 1` for every candidate
  `a`. (The converse, that the inequality suffices, is `Couplings.lemma3_suff`.)
* **Theorem 4** (`joint_unbeaten`, `no_joint_consistent`). A lottery rule that elects a Condorcet
  winner with certainty, and admits for every join of two electorates such a joint draw of the
  winners at the two electorates and at their union, gives probability zero to every candidate
  whom another candidate beats by majority. So there is no such rule as soon as some electorate
  has every candidate beaten, as at a majority cycle on three candidates.

Setting. An electorate is a finite list of ballots with nonnegative real weights (vote shares
need not sum to one); joining two electorates appends the lists. A ballot gives each candidate a
position, smaller is better, so ties are allowed, as in `Consistency.lean`. Neither anonymity nor
homogeneity is assumed: the rule is a function on weighted lists.

Construction, after Theorem 2 (`Consistency.lean`). Let `w` beat `x` at `p` with margin `d > 0`,
and let `W` be the total weight of `p`. The electorate `q` gives weight `A = (W+1)/2 + d/4` to
the ballot `x w (rest)` and `B = (W+1)/2 − d/4` to `w x (rest)`. Then `x` is the Condorcet winner
of `q`, and `w` is the Condorcet winner of `p` joined with `q`. Lemma 3 gives
`L(p+q)(x) ≥ L(p)(x) + L(q)(x) − 1 = L(p)(x)`, and the left side is 0.
-/

open Finset

namespace JoinLotteries

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Lemma 3, necessary direction -/

/-- A joint draw of `X ~ μ`, `Y ~ ν`, `Z ~ lam` with `X = Y → Z = X`. -/
def JointDraw3 (μ ν lam : α → ℝ) : Prop :=
  ∃ P : α → α → α → ℝ, (∀ x y z, 0 ≤ P x y z) ∧ (∀ x, ∑ y, ∑ z, P x y z = μ x) ∧
    (∀ y, ∑ x, ∑ z, P x y z = ν y) ∧ (∀ z, ∑ x, ∑ y, P x y z = lam z) ∧
    (∀ x z, P x x z ≠ 0 → z = x)

theorem lemma3_nec {μ ν lam : α → ℝ} (hν : ∑ y, ν y = 1) (h : JointDraw3 μ ν lam) (a : α) :
    μ a + ν a - 1 ≤ lam a := by
  obtain ⟨P, h0, hX, hY, hZ, hs⟩ := h
  have hoff : ∀ z, z ≠ a → P a a z = 0 := fun z hz => by
    by_contra hne
    exact hz (hs a z hne)
  have hdiag : ∑ z, P a a z = P a a a := Fintype.sum_eq_single a hoff
  have hl : P a a a ≤ lam a := by
    calc P a a a ≤ ∑ y, P a y a :=
          single_le_sum (f := fun y => P a y a) (fun y _ => h0 a y a) (mem_univ a)
      _ ≤ ∑ x, ∑ y, P x y a :=
          single_le_sum (f := fun x => ∑ y, P x y a)
            (fun x _ => sum_nonneg (fun y _ => h0 x y a)) (mem_univ a)
      _ = lam a := hZ a
  have hrow : ∀ y, ∑ z, P a y z ≤ ν y := by
    intro y
    calc ∑ z, P a y z ≤ ∑ x, ∑ z, P x y z :=
          single_le_sum (f := fun x => ∑ z, P x y z)
            (fun x _ => sum_nonneg (fun z _ => h0 x y z)) (mem_univ a)
      _ = ν y := hY y
  have hμ : μ a = ∑ z, P a a z + ∑ y ∈ univ.erase a, ∑ z, P a y z := by
    rw [add_sum_erase univ (fun y => ∑ z, P a y z) (mem_univ a)]
    exact (hX a).symm
  have hν' : ν a + ∑ y ∈ univ.erase a, ν y = 1 := by
    rw [add_sum_erase univ ν (mem_univ a)]
    exact hν
  have hle : ∑ y ∈ univ.erase a, ∑ z, P a y z ≤ ∑ y ∈ univ.erase a, ν y :=
    sum_le_sum (fun y _ => hrow y)
  linarith

/-! ### Electorates -/

/-- A ballot: positions, smaller is better; ties allowed. -/
abbrev Ballot (α : Type*) := α → ℕ

/-- An electorate: ballots with weights. -/
abbrev Elec (α : Type*) := List (Ballot α × ℝ)

/-- Nonnegative weights. -/
def Valid (p : Elec α) : Prop := ∀ e ∈ p, 0 ≤ e.2

/-- Weight of the ballots ranking `a` strictly above `b`. -/
def sup (p : Elec α) (a b : α) : ℝ := (p.map (fun e => if e.1 a < e.1 b then e.2 else 0)).sum

/-- Total weight. -/
def total (p : Elec α) : ℝ := (p.map Prod.snd).sum

/-- `a` beats `b` by majority. -/
def beats (p : Elec α) (a b : α) : Prop := sup p b a < sup p a b

/-- `x` is the Condorcet winner. -/
def CW (p : Elec α) (x : α) : Prop := ∀ t, t ≠ x → beats p x t

omit [Fintype α] [DecidableEq α] in
@[simp] lemma sup_nil (a b : α) : sup ([] : Elec α) a b = 0 := by simp [sup]

omit [Fintype α] [DecidableEq α] in
lemma sup_cons (e : Ballot α × ℝ) (p : Elec α) (a b : α) :
    sup (e :: p) a b = (if e.1 a < e.1 b then e.2 else 0) + sup p a b := by
  simp [sup]

omit [Fintype α] [DecidableEq α] in
lemma total_cons (e : Ballot α × ℝ) (p : Elec α) : total (e :: p) = e.2 + total p := by
  simp [total]

omit [Fintype α] [DecidableEq α] in
lemma sup_append (p q : Elec α) (a b : α) : sup (p ++ q) a b = sup p a b + sup q a b := by
  simp [sup, List.sum_append]

omit [Fintype α] [DecidableEq α] in
lemma sup_bounds : ∀ p : Elec α, Valid p → ∀ a b, 0 ≤ sup p a b ∧ sup p a b ≤ total p
  | [], _, a, b => by simp [total]
  | e :: p, hp, a, b => by
    have he : 0 ≤ e.2 := hp e (by simp)
    have ih := sup_bounds p (fun e' h' => hp e' (by simp [h'])) a b
    rw [sup_cons, total_cons]
    split_ifs <;> constructor <;> linarith [ih.1, ih.2]

omit [Fintype α] [DecidableEq α] in
lemma valid_append {p q : Elec α} (hp : Valid p) (hq : Valid q) : Valid (p ++ q) := by
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hp e h
  · exact hq e h

/-! ### The counter-electorate -/

/-- The ballot `x w (rest)`. -/
def b1 (x w : α) : Ballot α := fun t => if t = x then 0 else if t = w then 1 else 2

/-- The ballot `w x (rest)`. -/
def b2 (x w : α) : Ballot α := fun t => if t = w then 0 else if t = x then 1 else 2

/-- Weight `A` on `x w (rest)`, weight `B` on `w x (rest)`. -/
def cq (x w : α) (A B : ℝ) : Elec α := [(b1 x w, A), (b2 x w, B)]

section Counter

variable {x w : α} (hxw : x ≠ w) (A B : ℝ)
include hxw

omit [Fintype α] in
lemma cq_xw : sup (cq x w A B) x w = A := by
  simp [cq, sup_cons, b1, b2, hxw, Ne.symm hxw]

omit [Fintype α] in
lemma cq_wx : sup (cq x w A B) w x = B := by
  simp [cq, sup_cons, b1, b2, hxw, Ne.symm hxw]

omit [Fintype α] in
lemma cq_xt {t : α} (htx : t ≠ x) (htw : t ≠ w) : sup (cq x w A B) x t = A + B := by
  simp [cq, sup_cons, b1, b2, hxw, htx, htw]

omit [Fintype α] in
lemma cq_tx {t : α} (htx : t ≠ x) (htw : t ≠ w) : sup (cq x w A B) t x = 0 := by
  simp [cq, sup_cons, b1, b2, hxw, htx, htw]

omit [Fintype α] in
lemma cq_wt {t : α} (htx : t ≠ x) (htw : t ≠ w) : sup (cq x w A B) w t = A + B := by
  simp [cq, sup_cons, b1, b2, Ne.symm hxw, htx, htw]

omit [Fintype α] in
lemma cq_tw {t : α} (htx : t ≠ x) (htw : t ≠ w) : sup (cq x w A B) t w = 0 := by
  simp [cq, sup_cons, b1, b2, Ne.symm hxw, htx, htw]

end Counter

/-! ### Theorem 4 -/

/-- Lottery rules: nonnegative lotteries summing to one on valid electorates. -/
structure LotteryRule (L : Elec α → α → ℝ) : Prop where
  nonneg : ∀ p, Valid p → ∀ a, 0 ≤ L p a
  total : ∀ p, Valid p → ∑ a, L p a = 1

/-- The Condorcet principle: a Condorcet winner is elected with certainty. -/
def CondorcetL (L : Elec α → α → ℝ) : Prop := ∀ p, Valid p → ∀ x, CW p x → L p x = 1

/-- Consistency for joint draws: for every join, a joint draw of the winners at the two
electorates and at their union with `X = Y → Z = X`. -/
def JointConsistent (L : Elec α → α → ℝ) : Prop :=
  ∀ p q, Valid p → Valid q → JointDraw3 (L p) (L q) (L (p ++ q))

lemma zero_of_one {L : Elec α → α → ℝ} (hL : LotteryRule L) {p : Elec α} (hp : Valid p)
    {w x : α} (hw : L p w = 1) (hxw : x ≠ w) : L p x = 0 := by
  have hs := hL.total p hp
  rw [← add_sum_erase univ (L p) (mem_univ w), hw] at hs
  have h0 : ∑ a ∈ univ.erase w, L p a = 0 := by linarith
  rw [sum_eq_zero_iff_of_nonneg (fun a _ => hL.nonneg p hp a)] at h0
  exact h0 x (mem_erase.mpr ⟨hxw, mem_univ x⟩)

/-- Theorem 4: a candidate beaten by majority gets probability zero. -/
theorem joint_unbeaten {L : Elec α → α → ℝ} (hL : LotteryRule L) (hC : CondorcetL L)
    (hJ : JointConsistent L) {p : Elec α} (hp : Valid p) {x w : α} (hwx : beats p w x) :
    L p x = 0 := by
  have hxw : x ≠ w := by
    intro h
    rw [h] at hwx
    exact lt_irrefl _ hwx
  unfold beats at hwx
  set W := total p with hW
  set d := sup p w x - sup p x w with hd
  obtain ⟨bxw1, bxw2⟩ := sup_bounds p hp x w
  obtain ⟨bwx1, bwx2⟩ := sup_bounds p hp w x
  have hd0 : 0 < d := by rw [hd]; linarith
  set A : ℝ := (W + 1) / 2 + d / 4 with hA
  set B : ℝ := (W + 1) / 2 - d / 4 with hB
  have hA0 : 0 ≤ A := by rw [hA]; linarith
  have hB0 : 0 ≤ B := by rw [hB]; linarith
  have hq : Valid (cq x w A B) := by
    intro e he
    simp [cq] at he
    rcases he with rfl | rfl
    · exact hA0
    · exact hB0
  -- x is the Condorcet winner of the counter-electorate
  have hcwq : CW (cq x w A B) x := by
    intro t htx
    unfold beats
    by_cases htw : t = w
    · rw [htw, cq_xw hxw, cq_wx hxw, hA, hB]
      linarith
    · rw [cq_xt hxw A B htx htw, cq_tx hxw A B htx htw, hA, hB]
      linarith
  -- w is the Condorcet winner of the join
  have hcwm : CW (p ++ cq x w A B) w := by
    intro t htw
    unfold beats
    rw [sup_append, sup_append]
    by_cases htx : t = x
    · rw [htx, cq_xw hxw, cq_wx hxw, hA, hB]
      linarith
    · rw [cq_wt hxw A B htx htw, cq_tw hxw A B htx htw, hA, hB]
      obtain ⟨_, btw2⟩ := sup_bounds p hp t w
      obtain ⟨bwt1, _⟩ := sup_bounds p hp w t
      linarith
  have hm : Valid (p ++ cq x w A B) := valid_append hp hq
  have hLq : L (cq x w A B) x = 1 := hC _ hq x hcwq
  have hLm : L (p ++ cq x w A B) x = 0 :=
    zero_of_one hL hm (hC _ hm w hcwm) hxw
  have key := lemma3_nec (hL.total _ hq) (hJ p (cq x w A B) hp hq) x
  rw [hLq, hLm] at key
  have := hL.nonneg p hp x
  linarith

/-- Hence no such rule exists as soon as some electorate has every candidate beaten. -/
theorem no_joint_consistent {L : Elec α → α → ℝ} (hL : LotteryRule L) (hC : CondorcetL L)
    (hJ : JointConsistent L) {p : Elec α} (hp : Valid p) (hall : ∀ a, ∃ w, beats p w a) :
    False := by
  have h1 := hL.total p hp
  have h0 : ∑ a, L p a = 0 := sum_eq_zero (fun a _ => by
    obtain ⟨w, hw⟩ := hall a
    exact joint_unbeaten hL hC hJ hp hw)
  linarith

end JoinLotteries
