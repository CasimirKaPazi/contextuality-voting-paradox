/-
  Lemmas 1–3 of *The Global Form: Arrow's Theorem as a Degree*
  (`notes/global-form.md`, Section 2): the discrete degree for three
  alternatives and any finite set of voters.

  The six rankings of a, b, c are the hexagon abc, bac, bca, cba, cab, acb
  (positions 0–5), consecutive rankings differing on one pair. A rule F sends
  profiles of positions to positions. When a set S of voters walks once around
  the hexagon together, the others fixed at c, the social ranking walks too,
  and its winding is `W F S c` (`wind` sums the steps ±1, so a full turn is 6).
  The degree of voter i is `deg F i c = W F {i} c / 6`.

  Method. Under independence of irrelevant alternatives (`IIA`) the social
  comparison on a pair depends only on the column on that pair. Along the walk
  of S it is therefore a function of S's bit on that pair: the walk is fixed by
  a table g of six bits (`gOf`, `W_eq`). Along a square of two blocks S and T
  it is fixed by a table h of twelve bits (`hOf`). What the note proves with
  squares on the hexagon becomes a finite statement about these tables, checked
  by `decide` for all 64 tables g (`checkG`) and all 4096 tables h (`checkH`):
  * a table of a ranking-valued walk winds 0 or 6, its steps are adjacent or
    still, and with winding 6 every pair flips with the walking bit;
  * the diagonal of a square of tables winds as much as one side plus the
    other (the staircase and the square of the note).

  Results:
  * `steps_adjacent`: the social walk moves to a neighbour or stands still;
  * `lemma1` (invariance): the degree does not depend on the context;
  * `lemma2` (sum): the diagonal winding is 6 times the sum of the degrees,
    and with unanimity the degrees sum to 1 (`degree_sum`);
  * `lemma3` (rigidity): every degree is 0 or 1, and a voter of degree 1 is
    pivotal on every pair at every context (`pivotal`). The note states
    −1, 0 or 1; for rules into rankings −1 does not occur, since the
    anti-dictatorship also has degree 1.
-/

module

public import Mathlib

@[expose] public section

open Finset

namespace GlobalForm

/-! ### The hexagon -/

/-- Comparisons on the pairs ab, ac, bc (rows) at the positions abc, bac, bca,
    cba, cab, acb (columns): `true` when the first is above the second. -/
def tbl : List (List Bool) :=
  [[true, false, false, false, true, true],
   [true, true, false, false, false, true],
   [true, true, true, false, false, false]]

def bit (e : Fin 3) (k : Fin 6) : Bool := (tbl.getD e.val []).getD k.val false

/-- The position with the given comparisons (abc for the two cyclic triples). -/
def decode (t : Fin 3 → Bool) : Fin 6 :=
  match t 0, t 1, t 2 with
  | true, true, true => 0
  | false, true, true => 1
  | false, false, true => 2
  | false, false, false => 3
  | true, false, false => 4
  | true, true, false => 5
  | _, _, _ => 0

/-- The comparisons form a ranking: not one of the two cycles. -/
def validB (t : Fin 3 → Bool) : Bool := !(t 0 && !t 1 && t 2) && !(!t 0 && t 1 && !t 2)

lemma decode_bits : ∀ p : Fin 6, decode (fun e => bit e p) = p := by decide

lemma valid_bits : ∀ p : Fin 6, validB (fun e => bit e p) = true := by decide

/-- A step: +1 forward, −1 backward, 0 otherwise. -/
def delta (a b : Fin 6) : ℤ := if b = a + 1 then 1 else if a = b + 1 then -1 else 0

lemma delta_self : ∀ a : Fin 6, delta a a = 0 := by decide

/-- The winding of a closed walk of six steps, in steps (a full turn is 6). -/
def wind (w : Fin 6 → Fin 6) : ℤ :=
  delta (w 0) (w 1) + delta (w 1) (w 2) + delta (w 2) (w 3) + delta (w 3) (w 4) +
    delta (w 4) (w 5) + delta (w 5) (w 0)

/-- Adjacent or equal positions. -/
def Adj (a b : Fin 6) : Prop := b = a ∨ b = a + 1 ∨ a = b + 1

/-! ### Tables and the finite checks -/

/-- The walk of a table g: at position k of the walkers, comparison e is g e (bit e k). -/
def walkG (g : Fin 3 → Bool → Bool) (k : Fin 6) : Fin 6 := decode fun e => g e (bit e k)

def Wg (g : Fin 3 → Bool → Bool) : ℤ := wind (walkG g)

/-- Every position of the walkers gives a ranking. -/
def ValidG (g : Fin 3 → Bool → Bool) : Prop := ∀ k : Fin 6, validB (fun e => g e (bit e k)) = true

def ValidH (h : Fin 3 → Bool → Bool → Bool) : Prop :=
  ∀ ka kb : Fin 6, validB (fun e => h e (bit e ka) (bit e kb)) = true

def CheckG (g : Fin 3 → Bool → Bool) : Prop :=
  ValidG g → (Wg g = 0 ∨ Wg g = 6) ∧ (Wg g ≠ 0 → ∀ e, g e true ≠ g e false) ∧
    ∀ k : Fin 6, Adj (walkG g k) (walkG g (k + 1))

def CheckH (h : Fin 3 → Bool → Bool → Bool) : Prop :=
  ValidH h → ∀ p q : Fin 6,
    Wg (fun e b => h e b b) = Wg (fun e b => h e b (bit e p)) + Wg (fun e b => h e (bit e q) b)

instance (g : Fin 3 → Bool → Bool) : Decidable (CheckG g) := by
  unfold CheckG ValidG Adj; infer_instance

instance (h : Fin 3 → Bool → Bool → Bool) : Decidable (CheckH h) := by
  unfold CheckH ValidH; infer_instance

def mkG (x0 x1 x2 x3 x4 x5 : Bool) : Fin 3 → Bool → Bool := fun e b =>
  match e.val, b with
  | 0, true => x0
  | 0, false => x1
  | 1, true => x2
  | 1, false => x3
  | 2, true => x4
  | _, _ => x5

def mkH (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 : Bool) : Fin 3 → Bool → Bool → Bool :=
  fun e a b =>
  match e.val, a, b with
  | 0, true, true => x0
  | 0, true, false => x1
  | 0, false, true => x2
  | 0, false, false => x3
  | 1, true, true => x4
  | 1, true, false => x5
  | 1, false, true => x6
  | 1, false, false => x7
  | 2, true, true => x8
  | 2, true, false => x9
  | 2, false, true => x10
  | _, _, _ => x11

def bools : List Bool := [true, false]

def allG : Bool :=
  bools.all fun x0 => bools.all fun x1 => bools.all fun x2 => bools.all fun x3 =>
  bools.all fun x4 => bools.all fun x5 => decide (CheckG (mkG x0 x1 x2 x3 x4 x5))

def allH : Bool :=
  bools.all fun x0 => bools.all fun x1 => bools.all fun x2 => bools.all fun x3 =>
  bools.all fun x4 => bools.all fun x5 => bools.all fun x6 => bools.all fun x7 =>
  bools.all fun x8 => bools.all fun x9 => bools.all fun x10 => bools.all fun x11 =>
  decide (CheckH (mkH x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11))

theorem allG_eq : allG = true := by decide +kernel

theorem allH_eq : allH = true := by decide +kernel

lemma all_bools {f : Bool → Bool} (h : bools.all f = true) (x : Bool) : f x = true := by
  cases x <;> simp_all [bools]

theorem checkG (g : Fin 3 → Bool → Bool) : CheckG g := by
  have h : decide (CheckG (mkG (g 0 true) (g 0 false) (g 1 true) (g 1 false) (g 2 true)
      (g 2 false))) = true :=
    all_bools (all_bools (all_bools (all_bools (all_bools (all_bools allG_eq
      (g 0 true)) (g 0 false)) (g 1 true)) (g 1 false)) (g 2 true)) (g 2 false)
  have hg : mkG (g 0 true) (g 0 false) (g 1 true) (g 1 false) (g 2 true) (g 2 false) = g := by
    funext e b
    fin_cases e <;> cases b <;> rfl
  rw [hg] at h
  exact of_decide_eq_true h

theorem checkH (h : Fin 3 → Bool → Bool → Bool) : CheckH h := by
  have hd : decide (CheckH (mkH (h 0 true true) (h 0 true false) (h 0 false true)
      (h 0 false false) (h 1 true true) (h 1 true false) (h 1 false true) (h 1 false false)
      (h 2 true true) (h 2 true false) (h 2 false true) (h 2 false false))) = true :=
    all_bools (all_bools (all_bools (all_bools (all_bools (all_bools (all_bools (all_bools
      (all_bools (all_bools (all_bools (all_bools allH_eq
      (h 0 true true)) (h 0 true false)) (h 0 false true)) (h 0 false false))
      (h 1 true true)) (h 1 true false)) (h 1 false true)) (h 1 false false))
      (h 2 true true)) (h 2 true false)) (h 2 false true)) (h 2 false false)
  have hh : mkH (h 0 true true) (h 0 true false) (h 0 false true) (h 0 false false)
      (h 1 true true) (h 1 true false) (h 1 false true) (h 1 false false)
      (h 2 true true) (h 2 true false) (h 2 false true) (h 2 false false) = h := by
    funext e a b
    fin_cases e <;> cases a <;> cases b <;> rfl
  rw [hh] at hd
  exact of_decide_eq_true hd

/-! ### Rules and their walks -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Independence of irrelevant alternatives: the social comparison on a pair
    depends only on the voters' comparisons on that pair. -/
def IIA (F : (ι → Fin 6) → Fin 6) : Prop :=
  ∀ e (π π' : ι → Fin 6), (∀ i, bit e (π i) = bit e (π' i)) → bit e (F π) = bit e (F π')

/-- Unanimity: if all voters hold one ranking, it is the social ranking. -/
def Unanimous (F : (ι → Fin 6) → Fin 6) : Prop := ∀ k, F (fun _ => k) = k

/-- The voters of S at position k, the others as in c. -/
def setS (S : Finset ι) (k : Fin 6) (c : ι → Fin 6) : ι → Fin 6 :=
  fun i => if i ∈ S then k else c i

/-- The winding of the social ranking while S walks once around, the others at c. -/
def W (F : (ι → Fin 6) → Fin 6) (S : Finset ι) (c : ι → Fin 6) : ℤ :=
  wind fun k => F (setS S k c)

/-- The degree of voter i at context c. -/
def deg (F : (ι → Fin 6) → Fin 6) (i : ι) (c : ι → Fin 6) : ℤ := W F {i} c / 6

/-- A position with every comparison `b`: abc for `true`, cba for `false`. -/
def rep (b : Bool) : Fin 6 := if b then 0 else 3

lemma bit_rep : ∀ (e : Fin 3) (b : Bool), bit e (rep b) = b := by decide

omit [Fintype ι] [DecidableEq ι] in
lemma F_decode (F : (ι → Fin 6) → Fin 6) (π : ι → Fin 6) {t : Fin 3 → Bool}
    (h : ∀ e, bit e (F π) = t e) : F π = decode t := by
  have : t = fun e => bit e (F π) := funext fun e => (h e).symm
  rw [this, decode_bits]

/-- The table of the walk of S at context c. -/
def gOf (F : (ι → Fin 6) → Fin 6) (S : Finset ι) (c : ι → Fin 6) : Fin 3 → Bool → Bool :=
  fun e b => bit e (F (setS S (rep b) c))

variable {F : (ι → Fin 6) → Fin 6}

omit [Fintype ι] in
lemma bit_setS (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) (k : Fin 6) (e : Fin 3) :
    bit e (F (setS S k c)) = gOf F S c e (bit e k) := by
  show bit e (F (setS S k c)) = bit e (F (setS S (rep (bit e k)) c))
  apply hF e
  intro i
  unfold setS
  split_ifs
  · exact (bit_rep e (bit e k)).symm
  · rfl

omit [Fintype ι] in
lemma W_eq (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) : W F S c = Wg (gOf F S c) := by
  unfold W Wg walkG
  congr 1
  funext k
  exact F_decode F _ fun e => bit_setS hF S c k e

omit [Fintype ι] in
lemma walk_eq (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) (k : Fin 6) :
    F (setS S k c) = walkG (gOf F S c) k :=
  F_decode F _ fun e => bit_setS hF S c k e

omit [Fintype ι] in
lemma validG_of (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) : ValidG (gOf F S c) := by
  intro k
  have : (fun e => gOf F S c e (bit e k)) = fun e => bit e (F (setS S k c)) :=
    funext fun e => (bit_setS hF S c k e).symm
  rw [this]
  exact valid_bits _

/-- The table of the square of two blocks S and T at context c. -/
def hOf (F : (ι → Fin 6) → Fin 6) (S T : Finset ι) (c : ι → Fin 6) :
    Fin 3 → Bool → Bool → Bool :=
  fun e a b => bit e (F (setS T (rep b) (setS S (rep a) c)))

omit [Fintype ι] in
lemma bit_two (hF : IIA F) (S T : Finset ι) (c : ι → Fin 6) (ka kb : Fin 6) (e : Fin 3) :
    bit e (F (setS T kb (setS S ka c))) = hOf F S T c e (bit e ka) (bit e kb) := by
  show _ = bit e (F (setS T (rep (bit e kb)) (setS S (rep (bit e ka)) c)))
  apply hF e
  intro i
  unfold setS
  split_ifs <;> first | rfl | exact (bit_rep e _).symm

omit [Fintype ι] in
lemma validH_of (hF : IIA F) (S T : Finset ι) (c : ι → Fin 6) : ValidH (hOf F S T c) := by
  intro ka kb
  have : (fun e => hOf F S T c e (bit e ka) (bit e kb)) =
      fun e => bit e (F (setS T kb (setS S ka c))) :=
    funext fun e => (bit_two hF S T c ka kb e).symm
  rw [this]
  exact valid_bits _

omit [Fintype ι] in
lemma setS_union (S T : Finset ι) (k : Fin 6) (c : ι → Fin 6) :
    setS (S ∪ T) k c = setS T k (setS S k c) := by
  funext i
  unfold setS
  by_cases hT : i ∈ T <;> by_cases hS : i ∈ S <;> simp [hT, hS]

omit [Fintype ι] in
lemma setS_comm {S T : Finset ι} (hST : Disjoint S T) (k p : Fin 6) (c : ι → Fin 6) :
    setS S k (setS T p c) = setS T p (setS S k c) := by
  funext i
  unfold setS
  by_cases hS : i ∈ S
  · have hT : i ∉ T := Finset.disjoint_left.mp hST hS
    simp [hS, hT]
  · simp [hS]

omit [Fintype ι] in
lemma setS_self (j : ι) (c : ι → Fin 6) : setS {j} (c j) c = c := by
  funext i
  unfold setS
  by_cases h : i = j <;> simp [h]

omit [Fintype ι] in
/-- The square of two disjoint blocks: the joint walk winds as much as the
    walk of S plus the walk of T, wherever the other block stands. -/
theorem two_block (hF : IIA F) (S T : Finset ι) (hST : Disjoint S T) (c : ι → Fin 6)
    (p q : Fin 6) : W F (S ∪ T) c = W F S (setS T p c) + W F T (setS S q c) := by
  have hc := checkH (hOf F S T c) (validH_of hF S T c) p q
  have e1 : W F (S ∪ T) c = Wg (fun e b => hOf F S T c e b b) := by
    unfold W Wg walkG
    congr 1
    funext k
    rw [setS_union]
    exact F_decode F _ fun e => bit_two hF S T c k k e
  have e2 : W F S (setS T p c) = Wg (fun e b => hOf F S T c e b (bit e p)) := by
    unfold W Wg walkG
    congr 1
    funext k
    rw [setS_comm hST]
    exact F_decode F _ fun e => bit_two hF S T c k p e
  have e3 : W F T (setS S q c) = Wg (fun e b => hOf F S T c e (bit e q) b) := by
    unfold W Wg walkG
    congr 1
    funext k
    exact F_decode F _ fun e => bit_two hF S T c q k e
  rw [e1, e2, e3]
  exact hc

/-! ### Lemma 1: invariance -/

omit [Fintype ι] in
lemma W_upd (hF : IIA F) (S : Finset ι) (j : ι) (c : ι → Fin 6) (p : Fin 6) :
    W F S (setS {j} p c) = W F S c := by
  by_cases hj : j ∈ S
  · unfold W
    congr 1
    funext k
    congr 1
    funext i
    unfold setS
    by_cases hi : i ∈ S
    · simp [hi]
    · have : i ≠ j := fun h => hi (h ▸ hj)
      simp [hi, this]
  · have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
    have h1 := two_block hF S {j} hd c p 0
    have h2 := two_block hF S {j} hd c (c j) 0
    rw [setS_self] at h2
    linarith

/-- The winding of a block does not depend on where the other voters stand. -/
theorem W_indep (hF : IIA F) (S : Finset ι) (c c' : ι → Fin 6) : W F S c = W F S c' := by
  have key : ∀ U : Finset ι, W F S c = W F S (fun i => if i ∈ U then c' i else c i) := by
    intro U
    induction U using Finset.induction_on with
    | empty => simp
    | @insert j U _ ih =>
      rw [ih]
      have : (fun i => if i ∈ insert j U then c' i else c i) =
          setS {j} (c' j) (fun i => if i ∈ U then c' i else c i) := by
        funext i
        unfold setS
        by_cases hij : i = j
        · subst hij
          simp
        · simp [hij]
      rw [this, W_upd hF]
  have := key univ
  simpa using this

/-- **Lemma 1 (invariance).** The degree does not depend on the context. -/
theorem lemma1 (hF : IIA F) (i : ι) (c c' : ι → Fin 6) : deg F i c = deg F i c' := by
  unfold deg
  rw [W_indep hF {i} c c']

/-! ### Lemma 3: rigidity -/

omit [Fintype ι] in
/-- Along a voter's or a block's loop the social ranking moves to a neighbour
    or stands still. -/
theorem steps_adjacent (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) (k : Fin 6) :
    Adj (F (setS S k c)) (F (setS S (k + 1) c)) := by
  rw [walk_eq hF, walk_eq hF]
  exact (checkG _ (validG_of hF S c)).2.2 k

omit [Fintype ι] in
theorem W_cases (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) : W F S c = 0 ∨ W F S c = 6 := by
  rw [W_eq hF]
  exact (checkG _ (validG_of hF S c)).1

omit [Fintype ι] in
theorem six_deg (hF : IIA F) (i : ι) (c : ι → Fin 6) : W F {i} c = 6 * deg F i c := by
  unfold deg
  rcases W_cases hF {i} c with h | h <;> rw [h] <;> norm_num

omit [Fintype ι] in
/-- **Lemma 3 (rigidity).** Every degree is 0 or 1. -/
theorem lemma3 (hF : IIA F) (i : ι) (c : ι → Fin 6) : deg F i c = 0 ∨ deg F i c = 1 := by
  unfold deg
  rcases W_cases hF {i} c with h | h <;> rw [h] <;> norm_num

/-- A voter of non-zero degree is pivotal on every pair at every context: the
    social comparison differs between the voter at abc and at cba. -/
theorem pivotal (hF : IIA F) (i : ι) (c : ι → Fin 6) (h : deg F i c ≠ 0) (c' : ι → Fin 6)
    (e : Fin 3) : bit e (F (setS {i} 0 c')) ≠ bit e (F (setS {i} 3 c')) := by
  have hW : W F {i} c' ≠ 0 := by
    rw [six_deg hF, lemma1 hF i c' c]
    intro h'
    apply h
    omega
  rw [W_eq hF] at hW
  exact (checkG _ (validG_of hF {i} c')).2.1 hW e

/-! ### Lemma 2: the sum -/

omit [Fintype ι] in
lemma W_empty (c : ι → Fin 6) : W F ∅ c = 0 := by
  unfold W
  have : (fun k => F (setS ∅ k c)) = fun _ => F c := by
    funext k
    unfold setS
    simp
  rw [this]
  simp [wind, delta_self]

/-- The winding of a block is the sum of its voters' windings. -/
theorem W_sum (hF : IIA F) (S : Finset ι) (c : ι → Fin 6) :
    W F S c = ∑ i ∈ S, W F {i} c := by
  induction S using Finset.induction_on with
  | empty => simp [W_empty]
  | @insert j S hj ih =>
    rw [sum_insert hj, ← ih]
    have hd : Disjoint S {j} := Finset.disjoint_singleton_right.mpr hj
    have h := two_block hF S {j} hd c (c j) 0
    rw [setS_self] at h
    rw [show insert j S = S ∪ {j} by rw [Finset.insert_eq, Finset.union_comm], h,
      W_indep hF {j} (setS S 0 c) c]
    ring

/-- **Lemma 2 (sum).** The diagonal loop, all voters walking together, winds
    6 times the sum of the degrees. -/
theorem lemma2 (hF : IIA F) (c : ι → Fin 6) : W F univ c = 6 * ∑ i, deg F i c := by
  rw [W_sum hF, mul_sum]
  exact sum_congr rfl fun i _ => six_deg hF i c

lemma W_univ (hU : Unanimous F) (c : ι → Fin 6) : W F univ c = 6 := by
  unfold W
  have : (fun k => F (setS univ k c)) = fun k => k := by
    funext k
    unfold setS
    simp
    exact hU k
  rw [this]
  decide

/-- With unanimity the degrees sum to 1. -/
theorem degree_sum (hF : IIA F) (hU : Unanimous F) (c : ι → Fin 6) : ∑ i, deg F i c = 1 := by
  have := lemma2 hF c
  rw [W_univ hU] at this
  omega

end GlobalForm
