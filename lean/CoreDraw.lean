import Mathlib

/-!
# The draw of CORE: martingale, floors and the mean rule

Statements from the working note *CORE and the Formal Results* (`notes/core-connection.md`).

Participants form a type `V`; a stage of the removal process is the finite set `S` of participants
still in the draw. `avg S f` is the average of `f` over `S`, and the endowment of participant `i`
at `S` is the average of `i`'s utilities `U i j` for the ideals of the members `j` of `S`.

* **The fair call** (`avg_erase`, `fair_call`; Section 3). Averaging over the member removed by a
  call leaves the average unchanged: the endowments form a martingale along the removals. This is
  Theorem 1 of the CORE paper.
* **The participant left last is uniform** (`last_uniform`; Section 3). If `P S i` is defined by
  `P {j} i = [i = j]` and, for `|S| ≥ 2`, by averaging over the member removed, then
  `P S i = 1/|S|` for every member `i` of `S`.
* **Floors from stage-wise floors** (`floor`, `holding_ge_endowment`; Sections 3i and 3e). If a
  value assigned to each stage is the value of the ideal at a single member and is at least the
  average of its values one removal later, it is at least the endowment at every stage. With an
  excluded member keeping their veto over every later proposal, the value of the process has this
  property for every participant (*veto kept*, Section 3i).
* **The mean rule is safe** (`mean_erase`, `mean_safe`, `mean_rule_ge_endowment`; Section 3e).
  Ideals are points `p j` of a real vector space and `mean S p` is the mean of the ideals of the
  members. Averaging the means of the groups with one member removed gives the mean again. For
  every concave utility `f`, member or not, the mean of `S` is worth at least the call at `S`, and
  at least the endowment `avg S (f ∘ p)`.

* **The decomposition of holdings** (`holdings_decomposition`; Section 3a). For any values `h` on
  stages with `h {j} = u j`, the value at a stage `S` is the average of `u` over `S` plus the
  surpluses `h T − (call at T)` of the groups `T ⊆ S` of two or more, each divided by
  `C(|S|, |T|)`, the number of groups of that size. The step is a count: a group `T` is reached
  from `S` after one removal from exactly `|S| − |T|` of the sets `S ∖ {k}`, and
  `(|S| − |T|) · C(|S|, |T|) = |S| · C(|S| − 1, |T|)`.

* **No harm on a line** (`random_ballot_floor`, `line_star`, `line_ge_endowment`; Section 3b).
  Outcomes form a finite type `X`, a lottery is a function `L : X → ℝ`, and `eu L u` is its
  expected utility. The lemma: if every utility `u` in a class lies above a non-negative
  combination of the members' utilities plus a constant, with equality at the members' ideals,
  and every group's outcome is worth at least its call to each member, then the outcome from
  every group `S` is worth at least the random ballot over `S` to every `u` in the class. On a
  line with losses proportional to distance the condition holds, for members whose ideals are
  outcomes and for any other utility `b − a |x − q|` with `a ≥ 0`, whether or not `q` is an
  outcome.

Not formalised here: the proposition on concave loss (Section 3b), safe agreements as poolings
(Section 3f), and the computations.
-/

open Finset

namespace CoreDraw

variable {V : Type*} [DecidableEq V]

/-! ### Averages over a stage -/

/-- The average of `f` over the finite set `S`. -/
noncomputable def avg (S : Finset V) (f : V → ℝ) : ℝ := ((S.card : ℝ))⁻¹ * ∑ j ∈ S, f j

omit [DecidableEq V] in
lemma avg_mono (S : Finset V) {f g : V → ℝ} (h : ∀ k ∈ S, f k ≤ g k) : avg S f ≤ avg S g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum h) (inv_nonneg.mpr (Nat.cast_nonneg _))

omit [DecidableEq V] in
lemma avg_neg (S : Finset V) (f : V → ℝ) : avg S (fun k => -f k) = -avg S f := by
  unfold avg
  rw [Finset.sum_neg_distrib, mul_neg]

omit [DecidableEq V] in
lemma avg_singleton (j : V) (f : V → ℝ) : avg {j} f = f j := by
  simp [avg]

/-- Each member is missing from exactly one of the sets `S.erase k`. -/
lemma sum_sum_erase (S : Finset V) (f : V → ℝ) :
    ∑ k ∈ S, ∑ j ∈ S.erase k, f j = ((S.card : ℝ) - 1) * ∑ j ∈ S, f j := by
  have h : ∀ k ∈ S, ∑ j ∈ S.erase k, f j = ∑ j ∈ S, f j - f k :=
    fun k hk => Finset.sum_erase_eq_sub hk
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

/-- **The fair call.** Averaging over the member removed leaves the average unchanged. -/
lemma avg_erase (S : Finset V) (f : V → ℝ) (hS : 2 ≤ S.card) :
    avg S (fun k => avg (S.erase k) f) = avg S f := by
  have h1 : 1 ≤ S.card := by omega
  have hne : (S.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    intro h0
    linarith
  have hc : ∀ k ∈ S, ((S.erase k).card : ℝ)⁻¹ * ∑ j ∈ S.erase k, f j
      = ((S.card : ℝ) - 1)⁻¹ * ∑ j ∈ S.erase k, f j := by
    intro k hk
    rw [Finset.card_erase_of_mem hk, Nat.cast_sub h1, Nat.cast_one]
  unfold avg
  rw [Finset.sum_congr rfl hc, ← Finset.mul_sum, sum_sum_erase, inv_mul_cancel_left₀ hne]

/-! ### Floors from stage-wise floors -/

/-- Induction on the size of the stage, for `floor`. -/
theorem floor_aux (u : V → ℝ) (h : Finset V → ℝ) (h1 : ∀ j, h {j} = u j)
    (hstep : ∀ S : Finset V, 2 ≤ S.card → avg S (fun k => h (S.erase k)) ≤ h S) :
    ∀ n : ℕ, ∀ S : Finset V, S.card = n + 1 → avg S u ≤ h S := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have hS' : S.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS'
    exact le_of_eq (by rw [avg_singleton, h1])
  | succ n ih =>
    intro S hS
    have h2 : 2 ≤ S.card := by omega
    have hk : ∀ k ∈ S, avg (S.erase k) u ≤ h (S.erase k) := by
      intro k hk
      apply ih
      have := Finset.card_erase_of_mem hk
      omega
    calc avg S u = avg S (fun k => avg (S.erase k) u) := (avg_erase S u h2).symm
      _ ≤ avg S (fun k => h (S.erase k)) := avg_mono S hk
      _ ≤ h S := hstep S h2

/-- **Floors from stage-wise floors.** A value on stages that equals `u j` at the single member `j`
and is at least its own average one removal later is at least the average of `u` at every
nonempty stage. -/
theorem floor (u : V → ℝ) (h : Finset V → ℝ) (h1 : ∀ j, h {j} = u j)
    (hstep : ∀ S : Finset V, 2 ≤ S.card → avg S (fun k => h (S.erase k)) ≤ h S)
    (S : Finset V) (hS : S.Nonempty) : avg S u ≤ h S :=
  floor_aux u h h1 hstep (S.card - 1) S (by have := hS.card_pos; omega)

/-- The same with equality: a value that equals its own average one removal later is the
average of `u`. -/
theorem eq_of_step (u : V → ℝ) (h : Finset V → ℝ) (h1 : ∀ j, h {j} = u j)
    (hstep : ∀ S : Finset V, 2 ≤ S.card → h S = avg S (fun k => h (S.erase k)))
    (S : Finset V) (hS : S.Nonempty) : h S = avg S u := by
  apply le_antisymm
  · have key : avg S (fun j => -u j) ≤ -h S :=
      floor (fun j => -u j) (fun T => -h T) (fun j => by simp [h1])
        (fun T hT => by
          show avg T (fun k => -h (T.erase k)) ≤ -h T
          exact le_of_eq (by rw [avg_neg, hstep T hT]))
        S hS
    rw [avg_neg] at key
    linarith
  · exact floor u h h1 (fun T hT => (hstep T hT).ge) S hS

/-! ### The draw -/

/-- **The participant left last is uniform.** -/
theorem last_uniform (P : Finset V → V → ℝ) (h1 : ∀ j i, P {j} i = if i = j then 1 else 0)
    (hstep : ∀ S : Finset V, 2 ≤ S.card → ∀ i, P S i = avg S (fun k => P (S.erase k) i))
    (S : Finset V) (hS : S.Nonempty) (i : V) (hi : i ∈ S) : P S i = ((S.card : ℝ))⁻¹ := by
  have key : P S i = avg S (fun j => if i = j then 1 else 0) :=
    eq_of_step _ (fun T => P T i) (fun j => h1 j i) (fun T hT => hstep T hT i) S hS
  rw [key]
  simp [avg, Finset.sum_ite_eq, hi]

/-- The endowment of participant `i` at the stage `S`: the average of `i`'s utilities `U i j` for
the ideals of the members `j` of `S`. -/
noncomputable def endowment (U : V → V → ℝ) (S : Finset V) (i : V) : ℝ := avg S (U i)

/-- **The fair call** (Theorem 1 of the CORE paper): the expected endowment after a call equals
the endowment before it. -/
theorem fair_call (U : V → V → ℝ) (S : Finset V) (hS : 2 ≤ S.card) (i : V) :
    avg S (fun k => endowment U (S.erase k) i) = endowment U S i :=
  avg_erase S (U i) hS

/-- **Veto kept.** Let `h S i` be the value to participant `i` of the process when `S` is the set
of members still in the draws. If a single member enacts their ideal, and at every larger stage
every participant gets at least their average value one exclusion later (as when every
participant, excluded or not, must accept every proposal), then every participant holds at least
their endowment at every stage. -/
theorem holding_ge_endowment (U : V → V → ℝ) (h : Finset V → V → ℝ)
    (h1 : ∀ j i, h {j} i = U i j)
    (hstep : ∀ S : Finset V, 2 ≤ S.card → ∀ i, avg S (fun k => h (S.erase k) i) ≤ h S i)
    (S : Finset V) (hS : S.Nonempty) (i : V) : endowment U S i ≤ h S i :=
  floor (U i) (fun T => h T i) (fun j => h1 j i) (fun T hT => hstep T hT i) S hS

/-! ### The decomposition of holdings -/

omit [DecidableEq V] in
lemma avg_congr (S : Finset V) {f g : V → ℝ} (h : ∀ k ∈ S, f k = g k) : avg S f = avg S g := by
  unfold avg
  rw [Finset.sum_congr rfl h]

omit [DecidableEq V] in
lemma avg_add (S : Finset V) (f g : V → ℝ) :
    avg S (fun k => f k + g k) = avg S f + avg S g := by
  unfold avg
  rw [Finset.sum_add_distrib, mul_add]

/-- The value of a call at `S`, given the values `h` one removal later. -/
noncomputable def callValue (h : Finset V → ℝ) (S : Finset V) : ℝ := avg S (fun k => h (S.erase k))

/-- The surplus of `S` over its own call. -/
noncomputable def surplus (h : Finset V → ℝ) (S : Finset V) : ℝ := h S - callValue h S

/-- The surpluses of the groups of two or more inside `S`, each divided by the number of groups of
its size. -/
noncomputable def surplusSum (h : Finset V → ℝ) (S : Finset V) : ℝ :=
  ∑ T ∈ S.powerset, if 2 ≤ T.card then surplus h T / (S.card.choose T.card : ℝ) else 0

/-- A group `T ⊆ S` lies inside `S ∖ {k}` for exactly the `|S| − |T|` members `k` outside `T`. -/
lemma sum_erase_powerset (S : Finset V) (F : Finset V → ℝ) :
    ∑ k ∈ S, ∑ T ∈ (S.erase k).powerset, F T
      = ∑ T ∈ S.powerset, ((S.card : ℝ) - T.card) * F T := by
  have hiff : ∀ k T, k ∈ S ∧ T ∈ (S.erase k).powerset ↔ k ∈ S \ T ∧ T ∈ S.powerset := by
    intro k T
    simp only [Finset.mem_powerset, Finset.mem_sdiff, Finset.subset_iff, Finset.mem_erase]
    constructor
    · rintro ⟨hk, hT⟩
      exact ⟨⟨hk, fun hkT => (hT hkT).1 rfl⟩, fun x hx => (hT hx).2⟩
    · rintro ⟨⟨hk, hkT⟩, hT⟩
      exact ⟨hk, fun x hx => ⟨fun hxk => hkT (hxk ▸ hx), hT hx⟩⟩
  rw [Finset.sum_comm' hiff]
  apply Finset.sum_congr rfl
  intro T hT
  rw [Finset.sum_const, nsmul_eq_mul]
  congr 1
  have hsub : T ⊆ S := Finset.mem_powerset.mp hT
  have := Finset.card_sdiff_add_card_eq_card hsub
  have h2 : (S \ T).card = S.card - T.card := by omega
  rw [h2, Nat.cast_sub (Finset.card_le_card hsub)]

lemma aux_div (x y z w : ℝ) (hx : x ≠ 0) (hz : z ≠ 0) (hw : w ≠ 0) (h : w * x = z * y) :
    x⁻¹ * y / w = 1 / z := by
  rw [div_eq_div_iff hw hz]
  calc x⁻¹ * y * z = x⁻¹ * (z * y) := by ring
    _ = x⁻¹ * (w * x) := by rw [h]
    _ = 1 * w := by rw [mul_comm w x, ← mul_assoc, inv_mul_cancel₀ hx]

/-- The weights: `(|S| − |T|) / (|S| · C(|S| − 1, |T|)) = 1 / C(|S|, |T|)` for `|T| < |S|`. -/
lemma term_eq (s t : ℕ) (a : ℝ) (ht : t < s) :
    ((s : ℝ))⁻¹ * ((s : ℝ) - t) * (a / ((s - 1).choose t : ℝ)) = a / (s.choose t : ℝ) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  have e' : (m.choose t : ℝ) * ((m + 1 : ℕ) : ℝ) = ((m + 1).choose t : ℝ) * ((m + 1 - t : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_mul_succ_eq m t
  rw [Nat.cast_sub (show t ≤ m + 1 by omega)] at e'
  have hx : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hz : ((m + 1).choose t : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.choose_pos (show t ≤ m + 1 by omega)).ne'
  have hw : (m.choose t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.choose_pos (show t ≤ m by omega)).ne'
  calc ((m + 1 : ℕ) : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) - t) * (a / (m.choose t : ℝ))
      = (((m + 1 : ℕ) : ℝ)⁻¹ * (((m + 1 : ℕ) : ℝ) - t) / (m.choose t : ℝ)) * a := by ring
    _ = (1 / ((m + 1).choose t : ℝ)) * a := by rw [aux_div _ _ _ _ hx hz hw e']
    _ = a / ((m + 1).choose t : ℝ) := by ring

/-- Induction on the size of the stage, for `holdings_decomposition`. -/
theorem holdings_decomposition_aux (u : V → ℝ) (h : Finset V → ℝ) (h1 : ∀ j, h {j} = u j) :
    ∀ n : ℕ, ∀ S : Finset V, S.card = n + 1 → h S = avg S u + surplusSum h S := by
  intro n
  induction n with
  | zero =>
    intro S hS
    have hS' : S.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS'
    have h0 : surplusSum h {j} = 0 := by
      unfold surplusSum
      apply Finset.sum_eq_zero
      intro T hT
      have hT1 : T.card ≤ 1 := by
        have := Finset.card_le_card (Finset.mem_powerset.mp hT)
        simpa using this
      rw [ite_eq_right (show ¬ 2 ≤ T.card by omega)]
    rw [h0, avg_singleton, h1, add_zero]
  | succ n ih =>
    intro S hS
    have h2 : 2 ≤ S.card := by omega
    -- the induction hypothesis for the groups with one member removed
    have hk : ∀ k ∈ S, h (S.erase k) = avg (S.erase k) u
        + ∑ T ∈ (S.erase k).powerset,
            if 2 ≤ T.card then surplus h T / ((S.card - 1).choose T.card : ℝ) else 0 := by
      intro k hk
      have hc : (S.erase k).card = S.card - 1 := Finset.card_erase_of_mem hk
      rw [ih (S.erase k) (by omega)]
      unfold surplusSum
      rw [hc]
    have hcall : h S = surplus h S + avg S (fun k => h (S.erase k)) := by
      unfold surplus callValue
      ring
    have hsum : avg S (fun k => h (S.erase k)) = avg S u + ((S.card : ℝ))⁻¹ *
        ∑ T ∈ S.powerset, ((S.card : ℝ) - T.card) *
          (if 2 ≤ T.card then surplus h T / ((S.card - 1).choose T.card : ℝ) else 0) := by
      rw [avg_congr S hk, avg_add, avg_erase S u h2, ← sum_erase_powerset]
      rfl
    have hterm : ∀ T ∈ S.powerset,
        (if 2 ≤ T.card then surplus h T / (S.card.choose T.card : ℝ) else 0)
          = ((S.card : ℝ))⁻¹ * (((S.card : ℝ) - T.card) *
              (if 2 ≤ T.card then surplus h T / ((S.card - 1).choose T.card : ℝ) else 0))
            + (if T = S then surplus h S else 0) := by
      intro T hT
      have hsub := Finset.mem_powerset.mp hT
      by_cases hTS : T = S
      · subst hTS
        simp [Nat.choose_self, h2]
      · have hlt : T.card < S.card :=
          Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hTS⟩)
        rw [ite_eq_right hTS, add_zero]
        split_ifs with h2T
        · rw [← mul_assoc]
          exact (term_eq S.card T.card (surplus h T) hlt).symm
        · simp
    rw [hcall, hsum]
    unfold surplusSum
    rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_ite_eq',
      ite_eq_left (Finset.mem_powerset_self S)]
    ring

/-- **The decomposition of holdings** (Section 3a): the value at a nonempty stage is the average of
the values at the single members plus the surpluses of the groups of two or more inside it, each
divided by the number of groups of its size. With `h` the value of the process to one participant
and `u` that participant's utilities for the ideals, this is the endowment plus the weighted
surpluses. -/
theorem holdings_decomposition (u : V → ℝ) (h : Finset V → ℝ) (h1 : ∀ j, h {j} = u j)
    (S : Finset V) (hS : S.Nonempty) : h S = avg S u + surplusSum h S :=
  holdings_decomposition_aux u h h1 (S.card - 1) S (by have := hS.card_pos; omega)

/-! ### The mean rule -/

section Mean

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The mean of the ideals `p j` of the members of `S`. -/
noncomputable def mean (S : Finset V) (p : V → E) : E := ((S.card : ℝ))⁻¹ • ∑ j ∈ S, p j

omit [DecidableEq V] in
lemma mean_singleton (j : V) (p : V → E) : mean {j} p = p j := by
  simp [mean]

lemma sum_sum_erase_vec (S : Finset V) (p : V → E) :
    ∑ k ∈ S, ∑ j ∈ S.erase k, p j = ((S.card : ℝ) - 1) • ∑ j ∈ S, p j := by
  have h : ∀ k ∈ S, ∑ j ∈ S.erase k, p j = ∑ j ∈ S, p j - p k :=
    fun k hk => Finset.sum_erase_eq_sub hk
  rw [Finset.sum_congr rfl h, Finset.sum_sub_distrib, Finset.sum_const, sub_smul, one_smul,
    Nat.cast_smul_eq_nsmul]

/-- **The recursion of the mean rule.** The means of the groups with one member removed average to
the mean of the group. -/
lemma mean_erase (S : Finset V) (p : V → E) (hS : 2 ≤ S.card) :
    ((S.card : ℝ))⁻¹ • ∑ k ∈ S, mean (S.erase k) p = mean S p := by
  have h1 : 1 ≤ S.card := by omega
  have hne : (S.card : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ S.card := by exact_mod_cast hS
    intro h0
    linarith
  have hc : ∀ k ∈ S, mean (S.erase k) p = ((S.card : ℝ) - 1)⁻¹ • ∑ j ∈ S.erase k, p j := by
    intro k hk
    unfold mean
    rw [Finset.card_erase_of_mem hk, Nat.cast_sub h1, Nat.cast_one]
  rw [Finset.sum_congr rfl hc, ← Finset.smul_sum, sum_sum_erase_vec, inv_smul_smul₀ hne]
  rfl

/-- **The mean is worth at least the call**, for every concave utility. -/
theorem mean_safe {f : E → ℝ} (hf : ConcaveOn ℝ Set.univ f) (S : Finset V) (p : V → E)
    (hS : 2 ≤ S.card) :
    avg S (fun k => f (mean (S.erase k) p)) ≤ f (mean S p) := by
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hw : ∑ _k ∈ S, ((S.card : ℝ))⁻¹ = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne']
  have key : ∑ k ∈ S, ((S.card : ℝ))⁻¹ • f (mean (S.erase k) p)
      ≤ f (∑ k ∈ S, ((S.card : ℝ))⁻¹ • mean (S.erase k) p) :=
    hf.le_map_sum (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)) hw (fun _ _ => Set.mem_univ _)
  have hrhs : ∑ k ∈ S, ((S.card : ℝ))⁻¹ • mean (S.erase k) p = mean S p := by
    rw [← Finset.smul_sum]
    exact mean_erase S p hS
  rw [hrhs] at key
  unfold avg
  rw [Finset.mul_sum]
  simpa only [smul_eq_mul] using key

/-- **The mean rule is safe** (Section 3e): for every concave utility `f`, the mean of the ideals
of the members of `S` is worth at least the endowment at `S`, the average of `f` over their
ideals. With `f` the utility of any participant, member of `S` or not. -/
theorem mean_rule_ge_endowment {f : E → ℝ} (hf : ConcaveOn ℝ Set.univ f) (p : V → E)
    (S : Finset V) (hS : S.Nonempty) : avg S (fun j => f (p j)) ≤ f (mean S p) :=
  floor (fun j => f (p j)) (fun T => f (mean T p)) (fun j => by simp [mean_singleton])
    (fun T hT => mean_safe hf T p hT) S hS

end Mean

/-! ### No harm on a line -/

omit [DecidableEq V] in
lemma avg_lin (S : Finset V) (hS : S.Nonempty) (T : Finset V) (a : V → ℝ) (g : V → V → ℝ)
    (c : ℝ) : avg S (fun k => ∑ m ∈ T, a m * g m k + c) = ∑ m ∈ T, a m * avg S (g m) + c := by
  unfold avg
  have hc : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.card_pos.ne'
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm, mul_add,
    Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m _
    rw [← Finset.mul_sum]
    ring
  · rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

lemma abs_tri (a b : ℝ) : |a + b| ≤ |a| + |b| :=
  abs_le.mpr ⟨by linarith [neg_abs_le a, neg_abs_le b], by linarith [le_abs_self a, le_abs_self b]⟩

/-- A point `p` between `q₁` and `q₂`: distance to `p` is at most the mixture of the distances to
`q₁` and `q₂` that has mean `p`, with equality outside the open interval between them. -/
lemma abs_le_mix (p q₁ q₂ : ℝ) (h1 : q₁ ≤ p) (h2 : p ≤ q₂) :
    ∃ l : ℝ, 0 ≤ l ∧ l ≤ 1 ∧ ∀ y : ℝ,
      |y - p| ≤ l * |y - q₁| + (1 - l) * |y - q₂| ∧
      ((y ≤ q₁ ∨ q₂ ≤ y) → |y - p| = l * |y - q₁| + (1 - l) * |y - q₂|) := by
  by_cases heq : q₁ = q₂
  · refine ⟨1, zero_le_one, le_rfl, fun y => ?_⟩
    have hp : p = q₁ := le_antisymm (heq ▸ h2) h1
    subst hp
    simp
  · have hd : 0 < q₂ - q₁ := by
      have := lt_of_le_of_ne (h1.trans h2) heq
      linarith
    obtain ⟨l, hl⟩ : ∃ l : ℝ, l = (q₂ - p) / (q₂ - q₁) := ⟨_, rfl⟩
    have hl0 : 0 ≤ l := by
      rw [hl]
      exact div_nonneg (by linarith) hd.le
    have hl1 : l ≤ 1 := by
      rw [hl, div_le_one hd]
      linarith
    have hl' : l * (q₂ - q₁) = q₂ - p := by
      rw [hl]
      field_simp [hd.ne']
    have hp : p = l * q₁ + (1 - l) * q₂ := by linear_combination hl'
    refine ⟨l, hl0, hl1, fun y => ⟨?_, ?_⟩⟩
    · have hy : y - p = l * (y - q₁) + (1 - l) * (y - q₂) := by
        rw [hp]
        ring
      rw [hy]
      calc |l * (y - q₁) + (1 - l) * (y - q₂)| ≤ |l * (y - q₁)| + |(1 - l) * (y - q₂)| :=
            abs_tri _ _
        _ = l * |y - q₁| + (1 - l) * |y - q₂| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - l)]
    · rintro (hy | hy)
      · rw [abs_of_nonpos (by linarith : y - p ≤ 0), abs_of_nonpos (by linarith : y - q₁ ≤ 0),
          abs_of_nonpos (by linarith : y - q₂ ≤ 0), hp]
        ring
      · rw [abs_of_nonneg (by linarith : 0 ≤ y - p), abs_of_nonneg (by linarith : 0 ≤ y - q₁),
          abs_of_nonneg (by linarith : 0 ≤ y - q₂), hp]
        ring

/-- A point `p` left of `q`: distance to `p` is at most the distance to `q` plus `q − p`, with
equality right of `q`. -/
lemma abs_le_edge (y p q : ℝ) (h : p ≤ q) :
    |y - p| ≤ |y - q| + (q - p) ∧ (q ≤ y → |y - p| = |y - q| + (q - p)) := by
  constructor
  · calc |y - p| = |(y - q) + (q - p)| := by congr 1; ring
      _ ≤ |y - q| + |q - p| := abs_tri _ _
      _ = |y - q| + (q - p) := by rw [abs_of_nonneg (by linarith : 0 ≤ q - p)]
  · intro hy
    rw [abs_of_nonneg (by linarith : 0 ≤ y - p), abs_of_nonneg (by linarith : 0 ≤ y - q)]
    ring

/-- The mirror of `abs_le_edge`: `p` right of `q`. -/
lemma abs_le_edge' (y p q : ℝ) (h : q ≤ p) :
    |y - p| ≤ |y - q| + (p - q) ∧ (y ≤ q → |y - p| = |y - q| + (p - q)) := by
  constructor
  · calc |y - p| = |(y - q) + (q - p)| := by congr 1; ring
      _ ≤ |y - q| + |q - p| := abs_tri _ _
      _ = |y - q| + (p - q) := by rw [abs_of_nonpos (by linarith : q - p ≤ 0)]; ring
  · intro hy
    rw [abs_of_nonpos (by linarith : y - p ≤ 0), abs_of_nonpos (by linarith : y - q ≤ 0)]
    ring

section Line

variable {X : Type*}

/-- Utility with loss proportional to distance on a line: `b − a |pos x − q|`. -/
noncomputable def lineUtil (b a q : ℝ) (pos : X → ℝ) (x : X) : ℝ := b - a * |pos x - q|

/-- Condition (∗) from a mixture of two members' distances (possibly the same member). -/
lemma star_of_mix (pos : X → ℝ) (ideal : V → X) (α β : V → ℝ) (hα : ∀ m, 0 < α m)
    (b a q : ℝ) (ha : 0 ≤ a) (S : Finset V) (m1 m2 : V) (hm1 : m1 ∈ S) (hm2 : m2 ∈ S)
    (l d : ℝ) (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hle : ∀ y : ℝ, |y - q| ≤ l * |y - pos (ideal m1)| + (1 - l) * |y - pos (ideal m2)| + d)
    (heq : ∀ k ∈ S, |pos (ideal k) - q| = l * |pos (ideal k) - pos (ideal m1)|
      + (1 - l) * |pos (ideal k) - pos (ideal m2)| + d) :
    ∃ w : V → ℝ, ∃ c : ℝ, (∀ m ∈ S, 0 ≤ w m) ∧
      (∀ x, ∑ m ∈ S, w m * lineUtil (β m) (α m) (pos (ideal m)) pos x + c
        ≤ lineUtil b a q pos x) ∧
      (∀ k ∈ S, lineUtil b a q pos (ideal k)
        = ∑ m ∈ S, w m * lineUtil (β m) (α m) (pos (ideal m)) pos (ideal k) + c) := by
  obtain ⟨w, hw⟩ : ∃ w : V → ℝ, w = fun m =>
      (if m = m1 then a * l / α m1 else 0) + (if m = m2 then a * (1 - l) / α m2 else 0) :=
    ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ,
      c = b - a * d - a * l * β m1 / α m1 - a * (1 - l) * β m2 / α m2 := ⟨_, rfl⟩
  have key : ∀ x, ∑ m ∈ S, w m * lineUtil (β m) (α m) (pos (ideal m)) pos x + c
      = b - a * (l * |pos x - pos (ideal m1)| + (1 - l) * |pos x - pos (ideal m2)| + d) := by
    intro x
    have k1 : a * l / α m1 * α m1 = a * l := by field_simp [(hα m1).ne']
    have k2 : a * (1 - l) / α m2 * α m2 = a * (1 - l) := by field_simp [(hα m2).ne']
    simp only [hw, hc, add_mul, ite_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
      hm1, hm2, ↓reduceIte, lineUtil]
    linear_combination (-|pos x - pos (ideal m1)|) * k1 + (-|pos x - pos (ideal m2)|) * k2
  refine ⟨w, c, ?_, ?_, ?_⟩
  · intro m _
    simp only [hw]
    apply add_nonneg
    · split_ifs
      · exact div_nonneg (mul_nonneg ha hl0) (hα m1).le
      · exact le_refl 0
    · split_ifs
      · exact div_nonneg (mul_nonneg ha (by linarith)) (hα m2).le
      · exact le_refl 0
  · intro x
    rw [key x]
    simp only [lineUtil]
    have := mul_le_mul_of_nonneg_left (hle (pos x)) ha
    linarith
  · intro k hk
    rw [key (ideal k)]
    simp only [lineUtil]
    rw [heq k hk]

/-- **Condition (∗) on a line** (Section 3b): every utility `b − a |x − q|` with `a ≥ 0` lies above
a non-negative combination of the members' utilities plus a constant, with equality at the
members' ideals. The members to combine are the nearest on each side of `q`, or the outermost
member when `q` lies beyond all of them. -/
lemma line_star (pos : X → ℝ) (ideal : V → X) (α β : V → ℝ) (hα : ∀ m, 0 < α m)
    (b a q : ℝ) (ha : 0 ≤ a) (S : Finset V) (hS : S.Nonempty) :
    ∃ w : V → ℝ, ∃ c : ℝ, (∀ m ∈ S, 0 ≤ w m) ∧
      (∀ x, ∑ m ∈ S, w m * lineUtil (β m) (α m) (pos (ideal m)) pos x + c
        ≤ lineUtil b a q pos x) ∧
      (∀ k ∈ S, lineUtil b a q pos (ideal k)
        = ∑ m ∈ S, w m * lineUtil (β m) (α m) (pos (ideal m)) pos (ideal k) + c) := by
  by_cases hL : (S.filter (fun m => pos (ideal m) ≤ q)).Nonempty
  · by_cases hG : (S.filter (fun m => q ≤ pos (ideal m))).Nonempty
    · -- members on both sides of `q`: the nearest on each side
      obtain ⟨m1, hm1, hmax⟩ := Finset.exists_max_image _ (fun m => pos (ideal m)) hL
      obtain ⟨m2, hm2, hmin⟩ := Finset.exists_min_image _ (fun m => pos (ideal m)) hG
      rw [Finset.mem_filter] at hm1 hm2
      obtain ⟨l, hl0, hl1, hmix⟩ := abs_le_mix q (pos (ideal m1)) (pos (ideal m2)) hm1.2 hm2.2
      refine star_of_mix pos ideal α β hα b a q ha S m1 m2 hm1.1 hm2.1 l 0 hl0 hl1 ?_ ?_
      · intro y
        rw [add_zero]
        exact (hmix y).1
      · intro k hk
        rw [add_zero]
        apply (hmix _).2
        by_cases hkq : pos (ideal k) ≤ q
        · left
          exact hmax k (Finset.mem_filter.mpr ⟨hk, hkq⟩)
        · right
          exact hmin k (Finset.mem_filter.mpr ⟨hk, (not_le.mp hkq).le⟩)
    · -- every member left of `q`: the rightmost member
      obtain ⟨m0, hm0, hmax⟩ := Finset.exists_max_image S (fun m => pos (ideal m)) hS
      have hq0 : pos (ideal m0) ≤ q := by
        by_contra h
        exact hG ⟨m0, Finset.mem_filter.mpr ⟨hm0, (not_le.mp h).le⟩⟩
      refine star_of_mix pos ideal α β hα b a q ha S m0 m0 hm0 hm0 1 (q - pos (ideal m0))
        zero_le_one le_rfl ?_ ?_
      · intro y
        have := (abs_le_edge' y q (pos (ideal m0)) hq0).1
        simp only [one_mul, sub_self, zero_mul, add_zero]
        linarith
      · intro k hk
        simp only [one_mul, sub_self, zero_mul, add_zero]
        exact (abs_le_edge' _ q _ hq0).2 (hmax k hk)
  · -- every member right of `q`: the leftmost member
    obtain ⟨m0, hm0, hmin⟩ := Finset.exists_min_image S (fun m => pos (ideal m)) hS
    have hq0 : q ≤ pos (ideal m0) := by
      by_contra h
      exact hL ⟨m0, Finset.mem_filter.mpr ⟨hm0, (not_le.mp h).le⟩⟩
    refine star_of_mix pos ideal α β hα b a q ha S m0 m0 hm0 hm0 1 (pos (ideal m0) - q)
      zero_le_one le_rfl ?_ ?_
    · intro y
      have := (abs_le_edge y q (pos (ideal m0)) hq0).1
      simp only [one_mul, sub_self, zero_mul, add_zero]
      linarith
    · intro k hk
      simp only [one_mul, sub_self, zero_mul, add_zero]
      exact (abs_le_edge _ q _ hq0).2 (hmin k hk)

end Line

section Lotteries

variable {X : Type*} [Fintype X]

/-- The expected utility of a lottery `L` on the finite set of outcomes. -/
noncomputable def eu (L : X → ℝ) (u : X → ℝ) : ℝ := ∑ x, L x * u x

lemma eu_mono (L : X → ℝ) (hL : ∀ x, 0 ≤ L x) {f g : X → ℝ} (h : ∀ x, f x ≤ g x) :
    eu L f ≤ eu L g := by
  unfold eu
  exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (h x) (hL x)

omit [DecidableEq V] in
lemma eu_lin (L : X → ℝ) (hL : ∑ x, L x = 1) (S : Finset V) (w : V → ℝ) (U : V → X → ℝ)
    (c : ℝ) : eu L (fun x => ∑ m ∈ S, w m * U m x + c) = ∑ m ∈ S, w m * eu L (U m) + c := by
  unfold eu
  have h1 : ∑ x, L x * ∑ m ∈ S, w m * U m x = ∑ m ∈ S, w m * ∑ x, L x * U m x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro _ _
    apply Finset.sum_congr rfl
    intro _ _
    ring
  have h2 : ∑ x, L x * c = c := by rw [← Finset.sum_mul, hL, one_mul]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, h1, h2]

/-- **The lemma behind the theorem for one dimension** (Section 3b). `R S` is the outcome law from
the group `S`; a call at `S` is worth the average of the values of `R (S ∖ {k})`, so `hIR` says
that every group's outcome, agreed or called, is worth at least its call to each member. If every
utility in the class `C` satisfies condition (∗), and the members' own utilities belong to `C`,
then the outcome from every group is worth at least the random ballot over its members to every
utility in `C`, member or not. -/
theorem random_ballot_floor (U : V → X → ℝ) (ideal : V → X) (R : Finset V → X → ℝ)
    (hR0 : ∀ S x, 0 ≤ R S x) (hR1 : ∀ S, ∑ x, R S x = 1)
    (h1 : ∀ j u, eu (R {j}) u = u (ideal j))
    (hIR : ∀ S : Finset V, 2 ≤ S.card → ∀ m ∈ S,
      avg S (fun k => eu (R (S.erase k)) (U m)) ≤ eu (R S) (U m))
    (C : Set (X → ℝ)) (hU : ∀ m, U m ∈ C)
    (hstar : ∀ u ∈ C, ∀ S : Finset V, S.Nonempty → ∃ w : V → ℝ, ∃ c : ℝ,
      (∀ m ∈ S, 0 ≤ w m) ∧ (∀ x, ∑ m ∈ S, w m * U m x + c ≤ u x) ∧
      (∀ k ∈ S, u (ideal k) = ∑ m ∈ S, w m * U m (ideal k) + c)) :
    ∀ n : ℕ, ∀ S : Finset V, S.card = n + 1 → ∀ u ∈ C,
      avg S (fun k => u (ideal k)) ≤ eu (R S) u := by
  intro n
  induction n with
  | zero =>
    intro S hS u _
    have hS' : S.card = 1 := by omega
    obtain ⟨j, rfl⟩ := Finset.card_eq_one.mp hS'
    simp [avg_singleton, h1]
  | succ n ih =>
    intro S hS
    have h2 : 2 ≤ S.card := by omega
    have hne : S.Nonempty := Finset.card_pos.mp (by omega)
    -- the members: individual rationality and the induction hypothesis
    have hmem : ∀ m ∈ S, avg S (fun k => U m (ideal k)) ≤ eu (R S) (U m) := by
      intro m hm
      calc avg S (fun k => U m (ideal k))
          = avg S (fun k => avg (S.erase k) (fun l => U m (ideal l))) :=
            (avg_erase S _ h2).symm
        _ ≤ avg S (fun k => eu (R (S.erase k)) (U m)) :=
            avg_mono S (fun k hk => ih (S.erase k)
              (by rw [Finset.card_erase_of_mem hk]; omega) (U m) (hU m))
        _ ≤ eu (R S) (U m) := hIR S h2 m hm
    -- everyone: condition (∗)
    intro u hu
    obtain ⟨w, c, hw, hle, heq⟩ := hstar u hu S hne
    have hs : ∑ m ∈ S, w m * avg S (fun k => U m (ideal k))
        ≤ ∑ m ∈ S, w m * eu (R S) (U m) :=
      Finset.sum_le_sum fun m hm => mul_le_mul_of_nonneg_left (hmem m hm) (hw m hm)
    calc avg S (fun k => u (ideal k))
        = avg S (fun k => ∑ m ∈ S, w m * U m (ideal k) + c) := avg_congr S heq
      _ = ∑ m ∈ S, w m * avg S (fun k => U m (ideal k)) + c :=
          avg_lin S hne S w (fun m k => U m (ideal k)) c
      _ ≤ ∑ m ∈ S, w m * eu (R S) (U m) + c := by linarith
      _ = eu (R S) (fun x => ∑ m ∈ S, w m * U m x + c) :=
          (eu_lin (R S) (hR1 S) S w U c).symm
      _ ≤ eu (R S) u := eu_mono (R S) (hR0 S) hle

/-- **The theorem for one dimension** (Section 3b). Outcomes are finitely many points `pos x` of a
line, member `m` has utility `β m − α m |pos x − pos (ideal m)|` with `α m > 0`, and every group's
outcome law `R S` is worth at least its call to each member. Then, to every utility
`b − a |pos x − q|` with `a ≥ 0`, the outcome from every group `S` is worth at least the random
ballot over `S`: no one, member or not, falls below their endowment at any stage. -/
theorem line_ge_endowment (pos : X → ℝ) (ideal : V → X) (α β : V → ℝ) (hα : ∀ m, 0 < α m)
    (R : Finset V → X → ℝ) (hR0 : ∀ S x, 0 ≤ R S x) (hR1 : ∀ S, ∑ x, R S x = 1)
    (h1 : ∀ j u, eu (R {j}) u = u (ideal j))
    (hIR : ∀ S : Finset V, 2 ≤ S.card → ∀ m ∈ S,
      avg S (fun k => eu (R (S.erase k)) (lineUtil (β m) (α m) (pos (ideal m)) pos))
        ≤ eu (R S) (lineUtil (β m) (α m) (pos (ideal m)) pos))
    (b a q : ℝ) (ha : 0 ≤ a) (S : Finset V) (hS : S.Nonempty) :
    avg S (fun k => lineUtil b a q pos (ideal k)) ≤ eu (R S) (lineUtil b a q pos) :=
  random_ballot_floor (fun m => lineUtil (β m) (α m) (pos (ideal m)) pos) ideal R hR0 hR1 h1 hIR
    {u | ∃ b a q : ℝ, 0 ≤ a ∧ u = lineUtil b a q pos}
    (fun m => ⟨β m, α m, pos (ideal m), (hα m).le, rfl⟩)
    (fun u hu S hS => by
      obtain ⟨b', a', q', ha', rfl⟩ := hu
      exact line_star pos ideal α β hα b' a' q' ha' S hS)
    (S.card - 1) S (by have := hS.card_pos; omega) (lineUtil b a q pos)
    ⟨b, a, q, ha, rfl⟩

end Lotteries

end CoreDraw
