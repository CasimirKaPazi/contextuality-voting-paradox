/-
  The call game as one tree: Section 3g of *CORE and the Formal Results*
  (`notes/core-connection.md`), parts 2 and 3, on top of the stages checked in
  `CoreDraw.lean`.

  The protocol. At every group S of two or more, a member k is drawn uniformly
  and proposes a lottery; the members vote; if all accept, the lottery is
  enacted, otherwise a member is drawn uniformly and removed and the game goes
  on at the smaller group. A single member enacts their ideal. Utilities `U m`
  are known; lotteries are functions `L : X → ℝ` on a finite set of outcomes,
  valued by `CoreDraw.eu`.

  Encoding. A profile (`Profile`) gives, for every group S and proposer k, a
  proposal, and for every proposal L, each member's vote: strategies depend on
  the group, the proposer and the proposal (Markov strategies). The outcome
  law `R` of a profile (`IsOutcome`) is the ideal at single members and, at a
  group of two or more, the average over the proposer of what the vote
  enacts (`result`): the proposal if all accept, otherwise the call
  `CoreDraw.callLaw R S`. A profile is a subgame-perfect equilibrium in
  undominated votes (`SPE`) when proposals are lotteries, every vote follows
  the acceptance rule of `CoreDraw.accept_weakly_dominant` (accept exactly
  what is worth at least the call), and no proposer gains by another lottery
  at any group: no profitable one-shot deviation at any node.

  * `spe_raiffa` (part 2): in every such equilibrium, the outcome at S is the
    average over the proposer of lotteries that are best for the proposer
    among those every member weakly prefers to the call (`BestAcc`): one step
    of Raiffa's procedure.
  * `exists_spe` (part 2, existence by backward induction): an equilibrium
    exists. Best acceptable lotteries exist by compactness of the simplex
    (`exists_best`), and the outcome law is built group size by group size
    (`approx`, `eqLaw`).
  * `spe_unique` (part 3): if each proposer's best acceptable lotteries all
    give every participant the same value, the equilibrium values are unique.

  On part 3: the hypothesis is needed for every participant, not only for
  the members of the group. A participant removed from S still has a value
  for the outcome of S, and that value enters their call at the larger
  groups that contain them.

  Not formalised: history-dependent strategies (the one-shot condition is
  taken as the definition of subgame perfection for Markov profiles), the
  equilibria without the undominated-vote refinement (part 1, all members
  calling), and the computations.
-/

module

public import Mathlib
public import CoreDraw

@[expose] public section

open Finset CoreDraw

namespace CallGame

variable {V : Type*} [DecidableEq V] {X : Type*} [Fintype X] [DecidableEq X]

/-! ### Lotteries and acceptable proposals -/

omit [DecidableEq X] in
/-- A lottery: non-negative weights summing to 1. -/
def IsLot (L : X → ℝ) : Prop := (∀ x, 0 ≤ L x) ∧ ∑ x, L x = 1

omit [DecidableEq V] in
/-- The ideal of the single member of S (for S = {j}, the point mass at `ideal j`). -/
def delta (ideal : V → X) (S : Finset V) : X → ℝ :=
  fun x => ∑ j ∈ S, if x = ideal j then 1 else 0

omit [DecidableEq X] in
/-- L is acceptable at S against the call values t: a lottery every member
    weakly prefers to the call. -/
def Acc (U : V → X → ℝ) (S : Finset V) (t : V → ℝ) (L : X → ℝ) : Prop :=
  IsLot L ∧ ∀ m ∈ S, t m ≤ eu L (U m)

omit [DecidableEq X] in
/-- P is a best acceptable lottery for the proposer k. -/
def BestAcc (U : V → X → ℝ) (S : Finset V) (t : V → ℝ) (k : V) (P : X → ℝ) : Prop :=
  Acc U S t P ∧ ∀ L, Acc U S t L → eu L (U k) ≤ eu P (U k)

omit [DecidableEq X] in
/-- The values of the call at S, given the outcome law R of the smaller groups. -/
noncomputable def thr (U : V → X → ℝ) (R : Finset V → X → ℝ) (S : Finset V) (m : V) : ℝ :=
  eu (callLaw R S) (U m)

omit [DecidableEq V] in
lemma isLot_delta (ideal : V → X) (j : V) : IsLot (delta ideal {j}) := by
  refine ⟨fun x => ?_, ?_⟩
  · simp only [delta, sum_singleton]
    split_ifs <;> norm_num
  · simp only [delta, sum_singleton]
    rw [sum_eq_single (ideal j) (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
    simp

omit [DecidableEq V] [DecidableEq X] in
/-- An average of lotteries is a lottery. -/
lemma isLot_avg (S : Finset V) (hS : S.Nonempty) (P : V → X → ℝ) (h : ∀ k ∈ S, IsLot (P k)) :
    IsLot (fun x => avg S (fun k => P k x)) := by
  refine ⟨fun x => ?_, ?_⟩
  · unfold avg
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _)) (sum_nonneg fun k hk => (h k hk).1 x)
  · unfold avg
    rw [← mul_sum, sum_comm, sum_congr rfl fun k hk => (h k hk).2, sum_const, nsmul_eq_mul,
      mul_one]
    exact inv_mul_cancel₀ (by exact_mod_cast hS.card_pos.ne')

omit [DecidableEq X] in
/-- The call is a lottery when the outcomes one removal later are. -/
lemma isLot_call (R : Finset V → X → ℝ) (S : Finset V) (hS : 2 ≤ S.card)
    (h : ∀ k ∈ S, IsLot (R (S.erase k))) : IsLot (callLaw R S) :=
  isLot_avg S (card_pos.mp (by omega)) (fun k => R (S.erase k)) h

/-! ### Profiles, outcomes and equilibria -/

/-- A Markov profile: proposals and votes depending on the group, the
    proposer and the proposal. -/
structure Profile (V X : Type*) where
  prop : Finset V → V → X → ℝ
  vote : Finset V → V → (X → ℝ) → V → Bool

omit [DecidableEq X] in
/-- What the vote at S enacts when k proposes L: L if every member accepts,
    otherwise the call. -/
noncomputable def result (σ : Profile V X) (R : Finset V → X → ℝ) (S : Finset V) (k : V)
    (L : X → ℝ) : X → ℝ :=
  if ∀ m ∈ S, σ.vote S k L m = true then L else callLaw R S

/-- R is the outcome law of σ: the ideal at single members, and at larger
    groups the average over the proposer of what the vote enacts. -/
structure IsOutcome (σ : Profile V X) (ideal : V → X) (R : Finset V → X → ℝ) : Prop where
  single : ∀ j, R {j} = delta ideal {j}
  step : ∀ S : Finset V, 2 ≤ S.card →
    R S = fun x => avg S (fun k => result σ R S k (σ.prop S k) x)

omit [DecidableEq X] in
/-- A subgame-perfect equilibrium in undominated votes: proposals are
    lotteries, votes follow the acceptance rule, and no proposer gains by
    another lottery. -/
structure SPE (U : V → X → ℝ) (σ : Profile V X) (R : Finset V → X → ℝ) : Prop where
  lot : ∀ S : Finset V, 2 ≤ S.card → ∀ k ∈ S, IsLot (σ.prop S k)
  vote : ∀ S k L m, σ.vote S k L m = decide (thr U R S m ≤ eu L (U m))
  prop : ∀ S : Finset V, 2 ≤ S.card → ∀ k ∈ S, ∀ L, IsLot L →
    eu (result σ R S k L) (U k) ≤ eu (result σ R S k (σ.prop S k)) (U k)

omit [DecidableEq X] in
/-- Under the acceptance rule a proposal is enacted exactly when it is acceptable. -/
lemma result_eq {U : V → X → ℝ} {σ : Profile V X} {R : Finset V → X → ℝ}
    (hv : ∀ S k L m, σ.vote S k L m = decide (thr U R S m ≤ eu L (U m)))
    (S : Finset V) (k : V) (L : X → ℝ) :
    result σ R S k L = if ∀ m ∈ S, thr U R S m ≤ eu L (U m) then L else callLaw R S := by
  unfold result
  simp only [hv, decide_eq_true_eq]

/-- The outcome law of a profile with lottery proposals is a lottery at every
    nonempty group. -/
lemma outcome_isLot {σ : Profile V X} {ideal : V → X} {R : Finset V → X → ℝ}
    (hp : ∀ S : Finset V, 2 ≤ S.card → ∀ k ∈ S, IsLot (σ.prop S k)) (hO : IsOutcome σ ideal R) :
    ∀ n, ∀ S : Finset V, S.card = n → S.Nonempty → IsLot (R S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS
    have h1 : 1 ≤ n := hn ▸ hS.card_pos
    rcases (by omega : n = 1 ∨ 2 ≤ n) with h | h
    · obtain ⟨j, rfl⟩ := card_eq_one.mp (hn.trans h)
      rw [hO.single j]
      exact isLot_delta ideal j
    · rw [hO.step S (hn ▸ h)]
      refine isLot_avg S hS _ fun k hk => ?_
      unfold result
      split_ifs
      · exact hp S (hn ▸ h) k hk
      · refine isLot_call R S (hn ▸ h) fun j hj => ?_
        have hc := card_erase_of_mem hj
        exact ih _ (by rw [hc]; omega) _ rfl (card_pos.mp (by rw [hc]; omega))

/-! ### Part 2: every equilibrium is one Raiffa step -/

/-- **Part 2.** In every subgame-perfect equilibrium in undominated votes, the
    outcome at a group of two or more is the average, over the drawn proposer,
    of lotteries that are best for the proposer among those every member
    weakly prefers to the call. -/
theorem spe_raiffa {U : V → X → ℝ} {σ : Profile V X} {ideal : V → X} {R : Finset V → X → ℝ}
    (hO : IsOutcome σ ideal R) (hσ : SPE U σ R) (S : Finset V) (hS : 2 ≤ S.card) :
    ∃ P : V → X → ℝ, (R S = fun x => avg S (fun k => P k x)) ∧
      ∀ k ∈ S, BestAcc U S (thr U R S) k (P k) := by
  have hC : IsLot (callLaw R S) := isLot_call R S hS fun j hj =>
    outcome_isLot hσ.lot hO _ _ rfl (card_pos.mp (by rw [card_erase_of_mem hj]; omega))
  have hCacc : Acc U S (thr U R S) (callLaw R S) := ⟨hC, fun m _ => le_refl _⟩
  refine ⟨fun k => result σ R S k (σ.prop S k), hO.step S hS, fun k hk => ⟨?_, fun L hL => ?_⟩⟩
  · show Acc U S (thr U R S) (result σ R S k (σ.prop S k))
    rw [result_eq hσ.vote]
    split_ifs with h
    · exact ⟨hσ.lot S hS k hk, h⟩
    · exact hCacc
  · have := hσ.prop S hS k hk L hL.1
    rwa [result_eq hσ.vote S k L, ite_eq_left hL.2] at this

/-! ### Existence by backward induction -/

omit [DecidableEq V] [DecidableEq X] in
/-- A best acceptable lottery exists: the acceptable lotteries form a compact
    set (closed, inside the cube [0, 1]^X) that contains the call, and
    expected utility is continuous. -/
lemma exists_best (U : V → X → ℝ) (S : Finset V) {C : X → ℝ} (hC : IsLot C) (k : V) :
    ∃ P, BestAcc U S (fun m => eu C (U m)) k P := by
  have hcont : ∀ u : X → ℝ, Continuous fun L : X → ℝ => eu L u := fun u => by
    unfold eu
    fun_prop
  let A : Set (X → ℝ) := {L | IsLot L ∧ ∀ m ∈ S, eu C (U m) ≤ eu L (U m)}
  have hAeq : A = ((⋂ x, {L : X → ℝ | 0 ≤ L x}) ∩ {L | ∑ x, L x = 1}) ∩
      ⋂ m, ⋂ (_ : m ∈ S), {L | eu C (U m) ≤ eu L (U m)} := by
    ext L
    simp [A, IsLot, and_assoc]
  have hAc : IsClosed A := by
    rw [hAeq]
    exact ((isClosed_iInter fun x => isClosed_le continuous_const (continuous_apply x)).inter
      (isClosed_eq (by fun_prop) continuous_const)).inter
      (isClosed_iInter fun m => isClosed_iInter fun _ =>
        isClosed_le continuous_const (hcont (U m)))
  have hAsub : A ⊆ Set.pi Set.univ (fun _ => Set.Icc (0 : ℝ) 1) := by
    intro L hL x _
    refine ⟨hL.1.1 x, ?_⟩
    have := single_le_sum (f := L) (fun y _ => hL.1.1 y) (mem_univ x)
    rw [hL.1.2] at this
    exact this
  have hA : IsCompact A :=
    (isCompact_univ_pi fun _ => isCompact_Icc).of_isClosed_subset hAc hAsub
  have hCA : C ∈ A := ⟨hC, fun m _ => le_refl _⟩
  obtain ⟨P, hPA, hmax⟩ := hA.exists_isMaxOn ⟨C, hCA⟩ (hcont (U k)).continuousOn
  exact ⟨P, hPA, fun L hL => isMaxOn_iff.mp hmax L hL⟩

open Classical in
/-- A chosen best acceptable lottery for the proposer k against the call C. -/
noncomputable def best (U : V → X → ℝ) (S : Finset V) (C : X → ℝ) (k : V) : X → ℝ :=
  if h : IsLot C then Classical.choose (exists_best U S h k) else C

omit [DecidableEq V] [DecidableEq X] in
lemma best_spec (U : V → X → ℝ) (S : Finset V) {C : X → ℝ} (hC : IsLot C) (k : V) :
    BestAcc U S (fun m => eu C (U m)) k (best U S C k) := by
  unfold best
  split_ifs
  exact Classical.choose_spec _

/-- The outcome law of backward induction, built group size by group size:
    `approx n` is correct on the groups of at most n members. -/
noncomputable def approx (U : V → X → ℝ) (ideal : V → X) : ℕ → Finset V → X → ℝ
  | 0 => fun S => delta ideal S
  | n + 1 => fun S =>
    if S.card = n + 1 ∧ 2 ≤ S.card then
      fun x => avg S (fun k => best U S (callLaw (approx U ideal n) S) k x)
    else approx U ideal n S

lemma approx_succ (U : V → X → ℝ) (ideal : V → X) (n : ℕ) (S : Finset V) :
    approx U ideal (n + 1) S =
      if S.card = n + 1 ∧ 2 ≤ S.card then
        fun x => avg S (fun k => best U S (callLaw (approx U ideal n) S) k x)
      else approx U ideal n S := rfl

lemma approx_stable (U : V → X → ℝ) (ideal : V → X) :
    ∀ n (S : Finset V), S.card ≤ n → approx U ideal n S = approx U ideal S.card S := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have h0 : S.card = 0 := by omega
    rw [h0]
  | succ n ih =>
    intro S hS
    by_cases hc : S.card = n + 1
    · rw [hc]
    · rw [approx_succ, ite_eq_right (fun h => hc h.1)]
      exact ih S (by omega)

/-- The outcome law of backward induction. -/
noncomputable def eqLaw (U : V → X → ℝ) (ideal : V → X) (S : Finset V) : X → ℝ :=
  approx U ideal S.card S

lemma eqLaw_single (U : V → X → ℝ) (ideal : V → X) (j : V) :
    eqLaw U ideal {j} = delta ideal {j} := by
  unfold eqLaw
  rw [card_singleton, show (1 : ℕ) = 0 + 1 from rfl, approx_succ,
    ite_eq_right (fun h => by have := h.2; rw [card_singleton] at this; omega)]
  rfl

lemma eqLaw_eq (U : V → X → ℝ) (ideal : V → X) (S : Finset V) (hS : 2 ≤ S.card) :
    eqLaw U ideal S = fun x => avg S (fun k => best U S (callLaw (eqLaw U ideal) S) k x) := by
  obtain ⟨n, hn⟩ : ∃ n, S.card = n + 1 := ⟨S.card - 1, by omega⟩
  have hc : callLaw (approx U ideal n) S = callLaw (eqLaw U ideal) S := by
    funext x
    simp only [callLaw]
    refine avg_congr S fun k hk => ?_
    have hcard : (S.erase k).card ≤ n := by rw [card_erase_of_mem hk]; omega
    rw [approx_stable U ideal n (S.erase k) hcard]
    rfl
  show approx U ideal S.card S = _
  rw [hn, approx_succ, ite_eq_left ⟨hn, hS⟩, hc]

lemma eqLaw_isLot (U : V → X → ℝ) (ideal : V → X) :
    ∀ n, ∀ S : Finset V, S.card = n → S.Nonempty → IsLot (eqLaw U ideal S) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS
    have h1 : 1 ≤ n := hn ▸ hS.card_pos
    rcases (by omega : n = 1 ∨ 2 ≤ n) with h | h
    · obtain ⟨j, rfl⟩ := card_eq_one.mp (hn.trans h)
      rw [eqLaw_single]
      exact isLot_delta ideal j
    · rw [eqLaw_eq U ideal S (hn ▸ h)]
      have hC : IsLot (callLaw (eqLaw U ideal) S) := isLot_call _ S (hn ▸ h) fun j hj => by
        have hc := card_erase_of_mem hj
        exact ih _ (by rw [hc]; omega) _ rfl (card_pos.mp (by rw [hc]; omega))
      exact isLot_avg S hS _ fun k _ => (best_spec U S hC k).1.1

/-- The profile of backward induction: propose a best acceptable lottery,
    accept exactly what is worth at least the call. -/
noncomputable def eqProfile (U : V → X → ℝ) (ideal : V → X) : Profile V X where
  prop S k := best U S (callLaw (eqLaw U ideal) S) k
  vote S _ L m := decide (eu (callLaw (eqLaw U ideal) S) (U m) ≤ eu L (U m))

/-- **Part 2, existence.** Backward induction gives a subgame-perfect
    equilibrium in undominated votes. -/
theorem exists_spe (U : V → X → ℝ) (ideal : V → X) :
    ∃ (σ : Profile V X) (R : Finset V → X → ℝ), IsOutcome σ ideal R ∧ SPE U σ R := by
  have hC : ∀ S : Finset V, 2 ≤ S.card → IsLot (callLaw (eqLaw U ideal) S) := fun S hS =>
    isLot_call _ S hS fun j hj =>
      eqLaw_isLot U ideal _ _ rfl (card_pos.mp (by rw [card_erase_of_mem hj]; omega))
  have hv : ∀ S k L m, (eqProfile U ideal).vote S k L m =
      decide (thr U (eqLaw U ideal) S m ≤ eu L (U m)) := fun _ _ _ _ => rfl
  have hprop : ∀ S : Finset V, 2 ≤ S.card → ∀ k,
      result (eqProfile U ideal) (eqLaw U ideal) S k ((eqProfile U ideal).prop S k) =
        (eqProfile U ideal).prop S k := fun S hS k => by
    rw [result_eq hv]
    exact ite_eq_left (best_spec U S (hC S hS) k).1.2
  refine ⟨eqProfile U ideal, eqLaw U ideal, ⟨eqLaw_single U ideal, fun S hS => ?_⟩,
    ⟨fun S hS k _ => (best_spec U S (hC S hS) k).1.1, hv, fun S hS k _ L hL => ?_⟩⟩
  · rw [eqLaw_eq U ideal S hS]
    funext x
    refine avg_congr S fun k _ => ?_
    rw [hprop S hS k]
    rfl
  · rw [hprop S hS k, result_eq hv]
    have hb := best_spec U S (hC S hS) k
    split_ifs with hacc
    · exact hb.2 L ⟨hL, hacc⟩
    · exact hb.2 _ ⟨hC S hS, fun m _ => le_refl _⟩

/-! ### Part 3: uniqueness of the values -/

/-- **Part 3.** If each proposer's best acceptable lotteries, against the
    calls of one equilibrium, all give every participant the same value, then
    every equilibrium gives every participant the same value at every group. -/
theorem spe_unique {U : V → X → ℝ} {ideal : V → X} {σ σ' : Profile V X}
    {R R' : Finset V → X → ℝ} (hO : IsOutcome σ ideal R) (hσ : SPE U σ R)
    (hO' : IsOutcome σ' ideal R') (hσ' : SPE U σ' R')
    (huniq : ∀ S : Finset V, 2 ≤ S.card → ∀ k ∈ S, ∀ P P',
      BestAcc U S (thr U R S) k P → BestAcc U S (thr U R S) k P' → ∀ m, eu P (U m) = eu P' (U m)) :
    ∀ n, ∀ S : Finset V, S.card = n → S.Nonempty → ∀ m, eu (R S) (U m) = eu (R' S) (U m) := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hn hS m
    have h1 : 1 ≤ n := hn ▸ hS.card_pos
    rcases (by omega : n = 1 ∨ 2 ≤ n) with h | h
    · obtain ⟨j, rfl⟩ := card_eq_one.mp (hn.trans h)
      rw [hO.single j, hO'.single j]
    · have h2 : 2 ≤ S.card := hn ▸ h
      -- the calls have the same values in both equilibria
      have hthr : thr U R' S = thr U R S := by
        funext m'
        unfold thr callLaw
        rw [eu_avg, eu_avg]
        refine avg_congr S fun j hj => ?_
        have hc := card_erase_of_mem hj
        exact (ih _ (by rw [hc]; omega) _ rfl (card_pos.mp (by rw [hc]; omega)) m').symm
      obtain ⟨P, hP, hPb⟩ := spe_raiffa hO hσ S h2
      obtain ⟨P', hP', hPb'⟩ := spe_raiffa hO' hσ' S h2
      rw [hP, hP', eu_avg, eu_avg]
      refine avg_congr S fun k hk => huniq S h2 k hk _ _ (hPb k hk) ?_ m
      rw [← hthr]
      exact hPb' k hk

end CallGame
