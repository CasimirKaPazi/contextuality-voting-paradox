/-
  The reduction proposition of *Consistency as an Extension Problem*
  (`notes/consistency-as-extension.md`, Section 3c).

  The scenario has the winner W(p) at each profile p as variables, and
  contexts of two kinds:
  * joins {p, q, p + q}, with the constraint "W(p) = W(q) implies
    W(p + q) = W(p)";
  * extensions {p, p + v} by one voter with ballot v, with the constraint that
    this voter weakly prefers W(p + v) to W(p).
  Profiles are multisets of rankings (anonymous rules), p + q is their union
  and p + v is `v ::ₘ p`. Which joins and extensions are contexts is left open
  (`Joins`, `Exts`), so that electorates of bounded size are covered.

  A weakly compatible family is a joint draw in each context whose marginal at
  each profile is the rule's lottery there. `reduction`: it exists exactly
  when the lotteries satisfy
  * (J) L(p + q)(a) ≥ L(p)(a) + L(q)(a) − 1 at every join, by Lemma 3
    (`Couplings.lemma3`), and
  * (E) L(p + v) first-order stochastically dominates L(p) with respect to v
    at every extension (`Dom`), by Strassen's theorem for a chain
    (`ext_iff_dom`, from `Couplings.mono_iff_dom` through the positions of v).

  `one_voter_join`: on a one-voter join {p, v, p + v}, where W(v) is v's top,
  (E) implies the join constraint.
-/

module

public import Couplings
public import GSTopTwo

@[expose] public section

open Finset PathPinning Couplings

namespace ConsistencyScenario

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### Extensions: stochastic dominance and monotone draws -/

/-- The first k candidates of the ranking v. -/
def topSeg (v : Rk α) (k : ℕ) : Finset α := univ.filter fun a => Rankings.pos v a < k

/-- ν first-order stochastically dominates μ with respect to v: every top
    segment of v has at least as much probability under ν. -/
def Dom (v : Rk α) (μ ν : α → ℝ) : Prop :=
  ∀ k, ∑ a ∈ topSeg v k, μ a ≤ ∑ a ∈ topSeg v k, ν a

/-- A joint draw of the winners without and with the voter v, in which v never
    gets a worse winner. -/
def ExtDraw (v : Rk α) (μ ν : α → ℝ) : Prop :=
  ∃ J : α → α → ℝ, (∀ a b, 0 ≤ J a b) ∧ (∀ a, ∑ b, J a b = μ a) ∧ (∀ b, ∑ a, J a b = ν b) ∧
    ∀ a b, J a b ≠ 0 → Rankings.pos v b ≤ Rankings.pos v a

/-- A draw in which v never loses makes the second lottery dominate. -/
theorem dom_of_ext {v : Rk α} {μ ν : α → ℝ} (h : ExtDraw v μ ν) : Dom v μ ν := by
  obtain ⟨J, h0, hr, hc, hs⟩ := h
  intro k
  unfold topSeg
  calc ∑ a ∈ univ.filter (fun a => Rankings.pos v a < k), μ a
        = ∑ a ∈ univ.filter (fun a => Rankings.pos v a < k), ∑ b, J a b :=
        sum_congr rfl fun a _ => (hr a).symm
    _ = ∑ a ∈ univ.filter (fun a => Rankings.pos v a < k),
          ∑ b ∈ univ.filter (fun b => Rankings.pos v b < k), J a b := by
        refine sum_congr rfl fun a ha => ?_
        have hz : ∑ b ∈ univ.filter (fun b => ¬ Rankings.pos v b < k), J a b = 0 := by
          refine sum_eq_zero fun b hb => ?_
          by_contra hne
          have := hs a b hne
          simp only [mem_filter, mem_univ, true_and] at ha hb
          omega
        rw [← sum_filter_add_sum_filter_not univ (fun b => Rankings.pos v b < k) (J a), hz,
          add_zero]
    _ ≤ ∑ a, ∑ b ∈ univ.filter (fun b => Rankings.pos v b < k), J a b :=
        sum_le_sum_of_subset_of_nonneg (subset_univ _)
          (fun a _ _ => sum_nonneg fun b _ => h0 a b)
    _ = ∑ b ∈ univ.filter (fun b => Rankings.pos v b < k), ∑ a, J a b := sum_comm
    _ = ∑ b ∈ univ.filter (fun b => Rankings.pos v b < k), ν b :=
        sum_congr rfl fun b _ => hc b

/-- A lottery read along the positions of v. -/
def seq (v : Rk α) (μ : α → ℝ) (i : ℕ) : ℝ :=
  ∑ a ∈ univ.filter (fun a => Rankings.pos v a = i), μ a

lemma seq_pos (v : Rk α) (μ : α → ℝ) (a : α) : seq v μ (Rankings.pos v a) = μ a := by
  unfold seq
  have : univ.filter (fun b => Rankings.pos v b = Rankings.pos v a) = {a} := by
    ext b
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => Rankings.pos_inj v h, fun h => h ▸ rfl⟩
  rw [this, sum_singleton]

lemma seq_nonneg (v : Rk α) {μ : α → ℝ} (h0 : ∀ a, 0 ≤ μ a) (i : ℕ) : 0 ≤ seq v μ i :=
  sum_nonneg fun a _ => h0 a

lemma cum_seq (v : Rk α) (μ : α → ℝ) (k : ℕ) : cum (seq v μ) k = ∑ a ∈ topSeg v k, μ a := by
  unfold cum seq topSeg
  rw [← sum_fiberwise_of_maps_to (s := univ.filter (fun a => Rankings.pos v a < k))
    (t := range k) (g := Rankings.pos v) (f := μ) (fun a ha => by simpa using ha)]
  refine sum_congr rfl fun j hj => ?_
  apply sum_congr _ (fun _ _ => rfl)
  ext a
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · intro h
    exact ⟨by rw [h]; exact mem_range.mp hj, h⟩
  · exact fun h => h.2

/-- Sums over candidates as sums over the positions of v. -/
lemma sum_pos (v : Rk α) (f : ℕ → ℝ) :
    ∑ b, f (Rankings.pos v b) = ∑ j ∈ range (Fintype.card α), f j :=
  Finset.sum_nbij (Rankings.pos v) (fun a _ => mem_range.mpr (GSTopTwo.pos_lt_card v a))
    (fun a _ b _ h => Rankings.pos_inj v h)
    (fun j hj => by
      obtain ⟨a, ha⟩ := GSTopTwo.pos_surj v (mem_range.mp (mem_coe.mp hj))
      exact ⟨a, mem_coe.mpr (mem_univ a), ha⟩)
    (fun _ _ => rfl)

/-- Dominance gives a draw in which v never loses: the quantile coupling along
    the positions of v. -/
theorem ext_of_dom {v : Rk α} {μ ν : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a)
    (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ a, ν a = 1) (h : Dom v μ ν) : ExtDraw v μ ν := by
  have huniv : topSeg v (Fintype.card α) = univ := by
    ext a
    simp [topSeg, GSTopTwo.pos_lt_card]
  have htot : cum (seq v μ) (Fintype.card α) = cum (seq v ν) (Fintype.card α) := by
    rw [cum_seq, cum_seq, huniv, hμ1, hν1]
  have hdom : ∀ k ≤ Fintype.card α, cum (seq v μ) k ≤ cum (seq v ν) k := by
    intro k _
    rw [cum_seq, cum_seq]
    exact h k
  obtain ⟨J, h0, hr, hc, hs⟩ :=
    mono_of_dom (seq_nonneg v hμ0) (seq_nonneg v hν0) htot hdom
  refine ⟨fun a b => J (Rankings.pos v a) (Rankings.pos v b), fun a b => h0 _ _, ?_, ?_,
    fun a b hne => hs _ _ hne⟩
  · intro a
    show ∑ b, J (Rankings.pos v a) (Rankings.pos v b) = μ a
    rw [sum_pos v (J (Rankings.pos v a)), hr _ (GSTopTwo.pos_lt_card v a), seq_pos]
  · intro b
    show ∑ a, J (Rankings.pos v a) (Rankings.pos v b) = ν b
    have e : ∑ a, J (Rankings.pos v a) (Rankings.pos v b) =
        ∑ i ∈ range (Fintype.card α), J i (Rankings.pos v b) :=
      sum_pos v (fun i => J i (Rankings.pos v b))
    rw [e, hc _ (GSTopTwo.pos_lt_card v b), seq_pos]

/-- **Strassen for a ballot.** For lotteries μ and ν, a draw in which the voter
    v never gets a worse winner exists exactly when ν stochastically dominates
    μ with respect to v. -/
theorem ext_iff_dom {v : Rk α} {μ ν : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a)
    (hμ1 : ∑ a, μ a = 1) (hν1 : ∑ a, ν a = 1) : ExtDraw v μ ν ↔ Dom v μ ν :=
  ⟨dom_of_ext, ext_of_dom hμ0 hν0 hμ1 hν1⟩

/-! ### The reduction proposition -/

/-- **The reduction proposition.** For a family of lotteries over profiles,
    and any sets of joins and of extensions taken as contexts, there is a joint
    draw in every context with the rule's lotteries as marginals exactly when
    (J) holds at every join and (E) at every extension. -/
theorem reduction (L : Multiset (Rk α) → α → ℝ) (hL0 : ∀ p a, 0 ≤ L p a)
    (hL1 : ∀ p, ∑ a, L p a = 1) (Joins : Multiset (Rk α) → Multiset (Rk α) → Prop)
    (Exts : Multiset (Rk α) → Rk α → Prop) :
    ((∀ p q, Joins p q → JoinLotteries.JointDraw3 (L p) (L q) (L (p + q))) ∧
      ∀ p v, Exts p v → ExtDraw v (L p) (L (v ::ₘ p))) ↔
    ((∀ p q, Joins p q → ∀ a, L p a + L q a - 1 ≤ L (p + q) a) ∧
      ∀ p v, Exts p v → Dom v (L p) (L (v ::ₘ p))) := by
  constructor
  · rintro ⟨hj, he⟩
    exact ⟨fun p q hpq => (lemma3 (hL0 p) (hL0 q) (hL0 _) (hL1 p) (hL1 q) (hL1 _)).mp (hj p q hpq),
      fun p v hpv => dom_of_ext (he p v hpv)⟩
  · rintro ⟨hj, he⟩
    exact ⟨fun p q hpq => (lemma3 (hL0 p) (hL0 q) (hL0 _) (hL1 p) (hL1 q) (hL1 _)).mpr (hj p q hpq),
      fun p v hpv => ext_of_dom (hL0 p) (hL0 _) (hL1 p) (hL1 _) (he p v hpv)⟩

/-- **One-voter joins.** If W(v) is v's top t, condition (E) at the extension
    {p, p + v} implies condition (J) at the join {p, v, p + v}. -/
theorem one_voter_join {v : Rk α} {μ ν : α → ℝ} (hμ0 : ∀ a, 0 ≤ μ a) (hν0 : ∀ a, 0 ≤ ν a)
    (hμ1 : ∑ a, μ a = 1) (h : Dom v μ ν) {t : α} (ht : Rankings.pos v t = 0) (a : α) :
    μ a + (if a = t then 1 else 0) - 1 ≤ ν a := by
  by_cases hat : a = t
  · subst hat
    have h1 : topSeg v 1 = {a} := by
      ext b
      simp only [topSeg, mem_filter, mem_univ, true_and, mem_singleton]
      constructor
      · intro hb
        exact Rankings.pos_inj v (by omega)
      · intro hb
        rw [hb, ht]
        omega
    have := h 1
    rw [h1, sum_singleton, sum_singleton] at this
    rw [ite_eq_left rfl]
    linarith
  · have hle : μ a ≤ 1 := by
      have := single_le_sum (fun b _ => hμ0 b) (mem_univ a)
      rwa [hμ1] at this
    rw [ite_eq_right hat]
    linarith [hν0 a]

end ConsistencyScenario
