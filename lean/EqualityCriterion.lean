/-
  Propositions 1 and 2 of *The Equality Criterion and Reversal*
  (`notes/equality-criterion.md`, Section 3).

  A family of rules, one for each size n of electorate (voters `Fin n`, strict
  rankings as ballots), passes the Equality Criterion (`Criterion`) if each
  rule is anonymous and, for every ballot b, adding b and its reverse to any
  profile leaves the outcome unchanged (`PairInvariant`). The new voters come
  first; by anonymity their place does not matter.

  * `prop1`: no family of lotteries over rankings is at every size an
    empirical model on Arrow's scenario (full probabilistic independence and
    unanimity, `ArrowGeneral.Model`) and passes the criterion. By Theorem 5′
    (`ArrowBase.theorem5'`) each rule is a mixture of dictatorships; anonymity
    makes the weights equal (`weights_equal`); then one voter ranking b gets b
    with probability 1, while b, its reverse and b again give 2/3.
  * `prop2`: with at least three alternatives, no family of decision schemes
    is at every size SD-strategy-proof, Pareto-optimal and passes the
    criterion. Gibbard's (1977) characterisation enters as the hypothesis
    `GSCorollary.Gibbard1977`, as in `GSCorollary.lean`. Pareto-optimality
    gives unanimity (`unanimous_of_pareto`), Corollary 2 (`GSCorollary.cor2`)
    a mixture of dictatorships, anonymity random dictatorship
    (`GSCorollary.anonymous_uniform`); the same two profiles then give
    probability 1 and 2/3 to the top of b.

  Only the sizes 1 and 3 are used, and only one ballot b with one profile:
  `prop1_sizes` and `prop2_sizes` assume the conditions at these sizes alone,
  anonymity only for three voters, and invariance only for the profile b
  extended by b and its reverse. `prop1` and `prop2` are the statements of the
  note, for families of every size.
-/

module

public import ArrowBase
public import GSCorollary

@[expose] public section

open Finset PathPinning

namespace EqualityCriterion

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ### The criterion -/

/-- Permuting the voters does not change the outcome. -/
def Anonymous {n : ℕ} {β : Type*} (R : (Fin n → Rk α) → β) : Prop :=
  ∀ (s : Equiv.Perm (Fin n)) (π : Fin n → Rk α), R (fun k => π (s k)) = R π

/-- Adding the ballots b and b' to any profile does not change the outcome. -/
def PairInvariant {β : Type*} (R : (n : ℕ) → (Fin n → Rk α) → β) (b b' : Rk α) : Prop :=
  ∀ (n : ℕ) (π : Fin n → Rk α), R (n + 2) (Matrix.vecCons b (Matrix.vecCons b' π)) = R n π

/-- The Equality Criterion on strict rankings: anonymity, and every ballot
    together with its reverse is ignored. -/
def Criterion {β : Type*} (R : (n : ℕ) → (Fin n → Rk α) → β) : Prop :=
  (∀ n, Anonymous (R n)) ∧ ∀ b, PairInvariant R b (ArrowGeneral.revRk b)

/-! ### Rankings and their reverses -/

/-- With two or more alternatives no ranking is its own reverse. -/
lemma rev_ne (hα : 2 ≤ Fintype.card α) (σ : Rk α) : ArrowGeneral.revRk σ ≠ σ := by
  intro h
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
  have e : σ.1 b a = σ.1 a b := congrArg (fun ρ : Rk α => ρ.1 a b) h
  rcases PathPinning.total σ hab with h1 | h1
  · have h' := PathPinning.asymm σ h1
    rw [e, h1] at h'
    exact Bool.false_ne_true h'.symm
  · have h' := PathPinning.asymm σ h1
    rw [← e, h1] at h'
    exact Bool.false_ne_true h'.symm

/-- The top of b is not the top of its reverse. -/
lemma not_isTop_rev (hα : 2 ≤ Fintype.card α) [Nonempty α] (b : Rk α) :
    ¬ GSCorollary.IsTop (ArrowGeneral.revRk b) (GSCorollary.topOf b) := by
  intro h
  obtain ⟨y, hy⟩ : ∃ y, y ≠ GSCorollary.topOf b := by
    obtain ⟨a, c, hac⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card α)
    by_cases ha : a = GSCorollary.topOf b
    · exact ⟨c, fun hc => hac (ha.trans hc.symm)⟩
    · exact ⟨a, ha⟩
  have h1 : b.1 y (GSCorollary.topOf b) = true := h y hy
  have h2 := PathPinning.asymm b (GSCorollary.topOf_spec b y hy)
  rw [h1] at h2
  exact Bool.noConfusion h2

/-! ### Proposition 1 -/

lemma mixture_val {n : ℕ} {μ : (Fin n → Rk α) → Rk α → ℝ} {w : Fin n → ℝ}
    (hmix : ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k)
    (π : Fin n → Rk α) (σ : Rk α) : μ π σ = ∑ k, if π k = σ then w k else 0 := by
  rw [hmix, Finset.sum_filter]

/-- An anonymous mixture of dictatorships gives every voter the same weight. -/
lemma weights_equal (hα : 2 ≤ Fintype.card α) {n : ℕ} {μ : (Fin n → Rk α) → Rk α → ℝ}
    {w : Fin n → ℝ} (hmix : ∀ π σ, μ π σ = ∑ k ∈ univ.filter (fun k => π k = σ), w k)
    (hanon : Anonymous μ) (k₁ k₂ : Fin n) : w k₁ = w k₂ := by
  obtain ⟨σ⟩ : Nonempty (Rk α) := ⟨ArrowGeneral.baseRk⟩
  -- voter `k₀` ranks σ, the others its reverse
  let P : Fin n → Fin n → Rk α := fun k₀ k => if k = k₀ then σ else ArrowGeneral.revRk σ
  have hval : ∀ k₀, μ (P k₀) σ = w k₀ := by
    intro k₀
    rw [mixture_val hmix, Fintype.sum_eq_single k₀]
    · simp [P]
    · intro k hk
      simp [P, hk, rev_ne hα σ]
  have hP : (fun k => P k₁ (Equiv.swap k₁ k₂ k)) = P k₂ := by
    funext k
    have e : (Equiv.swap k₁ k₂ k = k₁) ↔ k = k₂ := by
      rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
    simp only [P, e]
  have := congrFun (hanon (Equiv.swap k₁ k₂) (P k₁)) σ
  rw [hP, hval, hval] at this
  exact this.symm

/-- **Proposition 1, sizes 1 and 3.** Rules for one and for three voters
    that are empirical models on Arrow's scenario, the second anonymous, cannot
    agree on the profile b, reverse of b, b and the profile b, for any one
    ballot b. -/
theorem prop1_sizes (hα : 3 ≤ Fintype.card α) (R₁ : (Fin 1 → Rk α) → Rk α → ℝ)
    (R₃ : (Fin 3 → Rk α) → Rk α → ℝ) (hM₁ : ArrowGeneral.Model R₁)
    (hM₃ : ArrowGeneral.Model R₃) (hanon : Anonymous R₃) (b : Rk α)
    (hpair : R₃ ![b, ArrowGeneral.revRk b, b] = R₁ ![b]) : False := by
  have hα2 : 2 ≤ Fintype.card α := by omega
  obtain ⟨w1, -, hw1, hmix1⟩ := ArrowBase.theorem5' α hα R₁ hM₁
  obtain ⟨w3, -, hw3, hmix3⟩ := ArrowBase.theorem5' α hα R₃ hM₃
  -- one voter ranking b: b with probability 1
  have e1 : R₁ ![b] b = 1 := by
    rw [mixture_val hmix1]
    simpa using hw1
  -- b, its reverse, b: probability w₀ + w₂
  have e3 : R₃ ![b, ArrowGeneral.revRk b, b] b = w3 0 + w3 2 := by
    rw [mixture_val hmix3, Fin.sum_univ_three]
    simp [rev_ne hα2 b]
  have h := congrFun hpair b
  rw [e1, e3] at h
  rw [Fin.sum_univ_three] at hw3
  have h01 := weights_equal hα2 hmix3 hanon 0 1
  have h21 := weights_equal hα2 hmix3 hanon 2 1
  linarith

/-- **Proposition 1.** No family of lotteries over rankings, one for each size
    of electorate, satisfies full probabilistic independence and unanimity at
    every size and the Equality Criterion. -/
theorem prop1 (hα : 3 ≤ Fintype.card α) (R : (n : ℕ) → (Fin n → Rk α) → Rk α → ℝ)
    (hM : ∀ n, 0 < n → ArrowGeneral.Model (R n)) (hEC : Criterion R) : False := by
  obtain ⟨b⟩ : Nonempty (Rk α) := ⟨ArrowGeneral.baseRk⟩
  exact prop1_sizes hα (R 1) (R 3) (hM 1 one_pos) (hM 3 (by norm_num)) (hEC.1 3) b
    (hEC.2 b 1 ![b])

/-! ### Proposition 2 -/

section Prop2

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Pareto-optimality: no probability on an alternative that another
    alternative beats in every ballot. -/
def ParetoOptimal (L : (ι → Rk α) → α → ℝ) : Prop :=
  ∀ π x y, (∀ k, (π k).1 y x = true) → L π x = 0

omit [Fintype ι] [DecidableEq ι] in
/-- A Pareto-optimal decision scheme is unanimous. -/
lemma unanimous_of_pareto {L : (ι → Rk α) → α → ℝ} (hL1 : ∀ π, ∑ x, L π x = 1)
    (hP : ParetoOptimal L) : GSCorollary.Unanimous L := by
  intro π a ha
  have h0 : ∀ x ∈ (univ : Finset α), x ≠ a → L π x = 0 :=
    fun x _ hx => hP π x a (fun k => ha k x hx)
  rw [← hL1 π, Finset.sum_eq_single a h0 (fun h => absurd (mem_univ a) h)]

end Prop2

/-- **Proposition 2, sizes 1 and 3.** Given Gibbard's (1977) characterisation
    for three voters, decision schemes for one and for three voters that are
    Pareto-optimal, the second SD-strategy-proof and anonymous, cannot agree on
    the profile b, reverse of b, b and the profile b, for any one ballot b. For
    one voter neither strategy-proofness nor Gibbard's theorem is needed. -/
theorem prop2_sizes (hα : 3 ≤ Fintype.card α) (hG : GSCorollary.Gibbard1977 (Fin 3) α)
    (L₁ : (Fin 1 → Rk α) → α → ℝ) (L₃ : (Fin 3 → Rk α) → α → ℝ)
    (hL1₁ : ∀ π, ∑ x, L₁ π x = 1) (hpar₁ : ParetoOptimal L₁)
    (hL0₃ : ∀ π x, 0 ≤ L₃ π x) (hL1₃ : ∀ π, ∑ x, L₃ π x = 1)
    (hsp₃ : GSScenario.SDSPRule L₃) (hpar₃ : ParetoOptimal L₃) (hanon₃ : Anonymous L₃)
    (b : Rk α) (hpair : L₃ ![b, ArrowGeneral.revRk b, b] = L₁ ![b]) : False := by
  have hα2 : 2 ≤ Fintype.card α := by omega
  have : Nonempty α := Fintype.card_pos_iff.mp (by omega)
  -- one voter ranking b: its top with probability 1, by unanimity
  have e1 : L₁ ![b] (GSCorollary.topOf b) = 1 :=
    unanimous_of_pareto hL1₁ hpar₁ ![b] (GSCorollary.topOf b) fun k => by
      fin_cases k
      exact GSCorollary.topOf_spec b
  -- three voters: a mixture of dictatorships, by Corollary 2, with equal weights
  have : Nonempty (Fin 3) := ⟨0⟩
  obtain ⟨lam, -, hs, hL3⟩ := GSCorollary.cor2 hα (hG L₃ hL0₃ hL1₃ hsp₃)
    (unanimous_of_pareto hL1₃ hpar₃)
  have hanon : GSCorollary.Anonymous (GSCorollary.LD (α := α) lam) := by
    intro s π
    funext x
    rw [← hL3 (fun k => π (s k)) x, ← hL3 π x]
    exact congrFun (hanon₃ s π) x
  have hu : ∀ k, lam k = 1 / 3 := by
    intro k
    rw [GSCorollary.anonymous_uniform hα2 hs hanon k]
    norm_num [Fintype.card_fin]
  -- b, its reverse, b: the top of b with probability 2/3
  have e3 : L₃ ![b, ArrowGeneral.revRk b, b] (GSCorollary.topOf b) = lam 0 + lam 2 := by
    rw [hL3]
    unfold GSCorollary.LD
    rw [Fin.sum_univ_three]
    simp [GSCorollary.topOf_spec b, not_isTop_rev hα2 b]
  have h := congrFun hpair (GSCorollary.topOf b)
  rw [e1, e3, hu 0, hu 2] at h
  norm_num at h

/-- **Proposition 2.** With at least three alternatives, and given Gibbard's
    (1977) characterisation, no family of decision schemes, one for each size
    of electorate, is SD-strategy-proof and Pareto-optimal at every size and
    satisfies the Equality Criterion. -/
theorem prop2 (hα : 3 ≤ Fintype.card α) (hG : ∀ n, GSCorollary.Gibbard1977 (Fin n) α)
    (L : (n : ℕ) → (Fin n → Rk α) → α → ℝ)
    (hL0 : ∀ n π x, 0 ≤ L n π x) (hL1 : ∀ n π, ∑ x, L n π x = 1)
    (hsp : ∀ n, GSScenario.SDSPRule (L n)) (hpar : ∀ n, ParetoOptimal (L n))
    (hEC : Criterion L) : False := by
  obtain ⟨b⟩ : Nonempty (Rk α) := ⟨ArrowGeneral.baseRk⟩
  exact prop2_sizes hα (hG 3) (L 1) (L 3) (hL1 1) (hpar 1) (hL0 3) (hL1 3) (hsp 3) (hpar 3)
    (hEC.1 3) b (hEC.2 b 1 ![b])

end EqualityCriterion
