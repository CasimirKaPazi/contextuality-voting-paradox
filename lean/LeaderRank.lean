/-
  Proposition 3 of *Bounds from Criteria*
  (`notes/strategic-information/bounds.md`, Section 3), in the frame of
  `StrategicCount.lean` and `Certification.lean`: certifying the leader takes
  a strategic count of rank at least m − 1, not counting the size of the
  electorate, and at rank m − 1 the row space is the leader's row.

  Setting as in `Certification.lean`: types T with rankings `ρ t`, every
  ranking among the types, a strategic count M with whole entries. The leader
  is a candidate `a`; its comparisons are indexed by the other candidates
  `{x // x ≠ a}`, with margins `sgn (ρ t) a x` (+1 for a voter who prefers a).

  * `flip_exists`: for every x ≠ a there are two rankings with the same
    comparisons of a with every candidate other than x, and opposite
    comparisons of a with x. Start from the ranking with a at some position
    and x next to it, then exchange the two.
  * `margins_indep`: the m − 1 margins and the constant are linearly
    independent as functions of the ranking; `margins_indep_types` the same
    as functions of the type, since every ranking occurs.
  * `prop3`: if the strategic count certifies the leader, the count together
    with the size of the electorate has rank at least m (`withSize`), and
    the count alone rank at least m − 1 (`prop3'`, with `rank_withSize_le`).
    By Lemma 1 the margins and the size lie in the row space.
  * `prop3_rowspace`: if moreover the count with the size has rank at most m,
    as for a count of totals taken up to a constant, its row space is spanned
    by the leader's margins and the size, the leader's row of the matrix of
    pairwise counts.

  * `cor5` (Corollary 5): such a count keeps opposite voters equal: with
    `opp t` a type whose ranking is the reverse of that of t, every row of
    the count is odd in the sense of `OppositeVoters.lean`, since reversing a
    ranking reverses every margin (`sgn_rev`).

  Not here: that a count of totals has rank at most m − 1 (a matter of the
  convention, taken as the hypothesis of `prop3_rowspace` and `cor5`), and
  the count 2^(m−1) of Proposition 2.
-/

module

public import Mathlib
public import Certification
public import OppositeVoters

@[expose] public section

open Finset Matrix StrategicCount Certification Module

namespace LeaderRank

variable {m : ℕ}

/-! ### The margins against the leader are independent -/

/-- Two rankings that differ only in the comparison of a with x. -/
lemma flip_exists {a x : Fin m} (hax : a ≠ x) :
    ∃ σ₁ σ₂ : Equiv.Perm (Fin m), (∀ y, y ≠ x → sgn σ₁ a y = sgn σ₂ a y) ∧
      sgn σ₁ a x ≠ sgn σ₂ a x := by
  have hv : a.val ≠ x.val := fun h => hax (Fin.ext h)
  have ha := a.isLt
  have hx := x.isLt
  -- a position q next to a
  obtain ⟨q, hq⟩ : ∃ q : Fin m, q.val = a.val + 1 ∨ q.val + 1 = a.val := by
    by_cases h : a.val + 1 < m
    · exact ⟨⟨a.val + 1, h⟩, Or.inl rfl⟩
    · exact ⟨⟨a.val - 1, by omega⟩, Or.inr (by show a.val - 1 + 1 = a.val; omega)⟩
  have haq : a ≠ q := fun h => by subst h; omega
  -- σ₁ puts x at q and leaves a at a; σ₂ exchanges the two
  let σ₁ : Equiv.Perm (Fin m) := Equiv.swap x q
  let σ₂ : Equiv.Perm (Fin m) := σ₁.trans (Equiv.swap a q)
  have h1a : σ₁ a = a := Equiv.swap_apply_of_ne_of_ne hax haq
  have h1x : σ₁ x = q := Equiv.swap_apply_left x q
  have h2a : σ₂ a = q := by
    show Equiv.swap a q (σ₁ a) = q
    rw [h1a, Equiv.swap_apply_left]
  have h2x : σ₂ x = a := by
    show Equiv.swap a q (σ₁ x) = a
    rw [h1x, Equiv.swap_apply_right]
  refine ⟨σ₁, σ₂, fun y hy => ?_, ?_⟩
  · by_cases hya : y = a
    · subst hya
      simp [sgn]
    have hz1 : σ₁ y ≠ a := fun h => hya (σ₁.injective (h.trans h1a.symm))
    have hz2 : σ₁ y ≠ q := fun h => hy (σ₁.injective (h.trans h1x.symm))
    have h2y : σ₂ y = σ₁ y := Equiv.swap_apply_of_ne_of_ne hz1 hz2
    have hz1' : (σ₁ y).val ≠ a.val := fun h => hz1 (Fin.ext h)
    have hz2' : (σ₁ y).val ≠ q.val := fun h => hz2 (Fin.ext h)
    have hiff : a < σ₁ y ↔ q < σ₁ y := by
      rw [Fin.lt_def, Fin.lt_def]
      omega
    simp only [sgn, h1a, h2a, h2y, hiff]
  · simp only [sgn, h1a, h1x, h2a, h2x]
    have hqv : q.val ≠ a.val := fun h => haq (Fin.ext h).symm
    by_cases h : a < q
    · have : ¬ q < a := fun h' => absurd (h.trans h') (lt_irrefl _)
      simp [h, this]
    · have : q < a := by
        rw [Fin.lt_def] at h ⊢
        omega
      simp [h, this]

/-- **Independence.** The margins of the leader against the others and the
    constant are linearly independent as functions of the ranking. -/
lemma margins_indep (a : Fin m) (g : Option {x // x ≠ a} → ℚ)
    (h : ∀ σ : Equiv.Perm (Fin m), g none + ∑ e, g (some e) * (sgn σ a e : ℚ) = 0) :
    ∀ i, g i = 0 := by
  have hsome : ∀ e, g (some e) = 0 := fun e => by
    obtain ⟨σ₁, σ₂, hsame, hdiff⟩ := flip_exists (a := a) (x := e) (fun h => e.2 h.symm)
    have hsub : ∑ y, g (some y) * ((sgn σ₁ a y : ℚ) - sgn σ₂ a y) = 0 := by
      simp only [mul_sub, Finset.sum_sub_distrib]
      linarith [h σ₁, h σ₂]
    rw [Finset.sum_eq_single e] at hsub
    · rcases mul_eq_zero.mp hsub with h0 | h0
      · exact h0
      · exact absurd (by exact_mod_cast sub_eq_zero.mp h0) hdiff
    · intro y _ hye
      rw [hsame y.val (fun hv => hye (Subtype.ext hv)), sub_self, mul_zero]
    · intro he
      exact absurd (mem_univ e) he
  intro i
  cases i with
  | some e => exact hsome e
  | none =>
    have := h 1
    simp only [hsome, zero_mul, Finset.sum_const_zero, add_zero] at this
    exact this

/-! ### In the frame of the strategic count -/

variable {T ι : Type*} [Fintype T] (ρ : T → Equiv.Perm (Fin m))

/-- The size of the electorate and the margins of the leader, as functions of
    the type. -/
def leaderRow (a : Fin m) : Option {x // x ≠ a} → (T → ℚ)
  | none => fun _ => 1
  | some e => fun t => (sgn (ρ t) a e : ℚ)

omit [Fintype T] in
lemma margins_indep_types (hρ : Function.Surjective ρ) (a : Fin m) :
    LinearIndependent ℚ (leaderRow ρ a) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  apply margins_indep a g
  intro σ
  obtain ⟨t, ht⟩ := hρ σ
  have := congr_fun hg t
  rw [Fintype.sum_option] at this
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, leaderRow,
    Pi.zero_apply, mul_one, ht] at this
  exact this

lemma card_leader (a : Fin m) : Fintype.card (Option {x // x ≠ a}) = m := by
  rw [Fintype.card_option, Fintype.card_subtype, Finset.filter_ne', Finset.card_erase_of_mem
    (mem_univ a), card_univ, Fintype.card_fin]
  have := a.pos
  omega

variable [Fintype ι] [DecidableEq ι] [DecidableEq T]

/-- Under certification, the margins and the size lie in the row space of the
    count with the size. -/
lemma span_le (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e)) :
    Submodule.span ℚ (Set.range (leaderRow ρ a)) ≤
      Submodule.span ℚ (Set.range (qM (withSize M)).row) := by
  have hK : KerCond M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e) :=
    (lemma1 (E := {x // x ≠ a}) ρ hρ M (fun _ => a) (fun e => e.val)
      (fun e h => e.2 h.symm)).mp hC
  obtain ⟨K, hKM⟩ := (kerCond_iff_rows M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e)).mp hK
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  cases i with
  | none =>
    exact Submodule.subset_span ⟨none, funext fun t => by simp [qM, withSize, leaderRow, Matrix.row]⟩
  | some e =>
    have hrow : leaderRow ρ a (some e) = ∑ j, K e j • (qM (withSize M)).row j := by
      funext t
      have := congr_fun (congr_fun hKM e) t
      rw [qM_margM, Matrix.mul_apply] at this
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, smul_eq_mul, Matrix.row]
      exact this
    rw [hrow]
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **Proposition 3, with the size.** Certifying the leader takes a count that,
    with the size of the electorate, has rank at least m. -/
theorem prop3 (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e)) :
    m ≤ (qM (withSize M)).rank := by
  rw [Matrix.rank_eq_finrank_span_row]
  calc m = Fintype.card (Option {x // x ≠ a}) := (card_leader a).symm
    _ = finrank ℚ (Submodule.span ℚ (Set.range (leaderRow ρ a))) :=
        (finrank_span_eq_card (margins_indep_types ρ hρ a)).symm
    _ ≤ finrank ℚ (Submodule.span ℚ (Set.range (qM (withSize M)).row)) :=
        Submodule.finrank_mono (span_le ρ hρ M a hC)

omit [DecidableEq ι] [DecidableEq T] in
/-- Adding the size adds at most one to the rank. -/
lemma rank_withSize_le (M : Matrix ι T ℤ) : (qM (withSize M)).rank ≤ (qM M).rank + 1 := by
  rw [Matrix.rank_eq_finrank_span_row, Matrix.rank_eq_finrank_span_row]
  have hle : Submodule.span ℚ (Set.range (qM (withSize M)).row) ≤
      Submodule.span ℚ (Set.range (qM M).row) ⊔ Submodule.span ℚ {(1 : T → ℚ)} := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    cases i with
    | none =>
      exact Submodule.mem_sup_right (Submodule.subset_span (by
        show (qM (withSize M)).row none = 1
        funext t
        simp [qM, withSize, Matrix.row]))
    | some i =>
      exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, funext fun t => by
        simp [qM, withSize, Matrix.row]⟩)
  calc finrank ℚ (Submodule.span ℚ (Set.range (qM (withSize M)).row))
      ≤ finrank ℚ ↥(Submodule.span ℚ (Set.range (qM M).row) ⊔ Submodule.span ℚ {(1 : T → ℚ)}) :=
        Submodule.finrank_mono hle
    _ ≤ finrank ℚ (Submodule.span ℚ (Set.range (qM M).row)) +
          finrank ℚ (Submodule.span ℚ {(1 : T → ℚ)}) :=
        Submodule.finrank_add_le_finrank_add_finrank _ _
    _ ≤ _ := by
        have : finrank ℚ (Submodule.span ℚ {(1 : T → ℚ)}) ≤ 1 :=
          (finrank_span_le_card _).trans (by simp)
        omega

/-- **Proposition 3.** Certifying the leader takes a strategic count of rank at
    least m − 1, not counting the size of the electorate. -/
theorem prop3' (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e)) :
    m - 1 ≤ (qM M).rank := by
  have h1 := prop3 ρ hρ M a hC
  have h2 := rank_withSize_le M
  omega

/-- **Proposition 3, the leader's row.** If the count with the size has rank at
    most m and certifies the leader, its row space is spanned by the leader's
    margins and the size. -/
theorem prop3_rowspace (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e))
    (hr : (qM (withSize M)).rank ≤ m) :
    Submodule.span ℚ (Set.range (qM (withSize M)).row) =
      Submodule.span ℚ (Set.range (leaderRow ρ a)) := by
  have hle := span_le ρ hρ M a hC
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  have h1 : finrank ℚ (Submodule.span ℚ (Set.range (leaderRow ρ a))) = m := by
    rw [finrank_span_eq_card (margins_indep_types ρ hρ a), card_leader]
  have h2 := Submodule.finrank_mono hle
  rw [Matrix.rank_eq_finrank_span_row] at hr
  omega

/-! ### Corollary 5 -/

/-- Reversing a ranking reverses every margin. -/
lemma sgn_rev {σ σ' : Equiv.Perm (Fin m)} (h : ∀ y, σ' y = Fin.rev (σ y)) {a x : Fin m}
    (hax : a ≠ x) : sgn σ' a x = - sgn σ a x := by
  simp only [sgn, h, Fin.rev_lt_rev]
  have hne : σ a ≠ σ x := fun e => hax (σ.injective e)
  rcases lt_or_gt_of_ne hne with h1 | h1
  · simp [h1, not_lt.mpr h1.le]
  · simp [h1, not_lt.mpr h1.le]

/-- **Corollary 5.** A count that, with the size, has rank at most m and
    certifies the leader keeps opposite voters equal: every row is odd. -/
theorem cor5 (hρ : Function.Surjective ρ) (M : Matrix ι T ℤ) (a : Fin m)
    (hC : Certifies M (fun (e : {x // x ≠ a}) t => sgn (ρ t) a e))
    (hr : (qM (withSize M)).rank ≤ m) (opp : T → T)
    (hopp : ∀ t y, ρ (opp t) y = Fin.rev (ρ t y)) :
    Submodule.span ℚ (Set.range (qM (withSize M)).row) ≤ OppositeVoters.odd opp ⊤ := by
  rw [prop3_rowspace ρ hρ M a hC hr, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  refine Submodule.mem_inf.mpr ⟨Submodule.mem_top, ?_⟩
  rw [Submodule.mem_comap]
  cases i with
  | none =>
    have h1 : leaderRow ρ a none = (1 : T → ℚ) := rfl
    rw [h1, OppositeVoters.ev_one]
    exact Submodule.subset_span (Set.mem_singleton _)
  | some e =>
    have h0 : OppositeVoters.ev opp (leaderRow ρ a (some e)) = 0 := by
      funext t
      rw [OppositeVoters.ev_apply]
      simp only [leaderRow, Pi.zero_apply]
      rw [sgn_rev (hopp t) (fun h => e.2 h.symm)]
      push_cast
      ring
    rw [h0]
    exact Submodule.zero_mem _

end LeaderRank
