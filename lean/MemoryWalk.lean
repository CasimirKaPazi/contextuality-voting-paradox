module

public import Mathlib
public import LeaderRule
public import StrategicInformation

@[expose] public section

/-!
# The walk with memory as one statement, and positions as utilities

Statements from the working note *Strategic Information* (`notes/strategic-information.md`),
Sections 4b and 4c, joining `LeaderRule.lean` (ballots as positions, the best replies as
definitions) and `StrategicInformation.lean` (real utilities, weights of ties, the counting).

* **The walk with memory** (`IsWalk`, `memory_walk`). At round `t` the poll is `(L t, R t)`.
  A candidate is eligible at `t` if it is the current leader or has not led up to `t`; the round
  is *active* if some candidate other than the leader is eligible. In an active round the
  runner-up is eligible and differs from the leader, the next leader is the strict leader of the
  approval tally among the eligible candidates, and, if the next round is active too, the next
  runner-up is strictly second among the candidates eligible then, in the same tally. A round that
  is not active keeps the leader. With strict preferences and no pairwise ties between candidates
  (for instance an odd number of voters), and `S` a non-empty set of candidates each of whom beats
  every candidate outside it (the Smith set is one), the leader is constant from round
  `2 (|A| − 1)` on and lies in `S`. This is Proposition 4, parts 4 and 5, derived from the steps
  in `LeaderRule.lean` and the counting in `StrategicInformation.lean`.
* **Positions as utilities** (`one_le_gap`, `bridge_approval`). A voter whose ballot gives
  distinct positions to the candidates has, with minus the position as utility, utility differences
  of at least 1. In the finite corner with `2 δ D < 1`, the best approval ballot of
  `StrategicInformation.lean` is then the ballot `approve` of `LeaderRule.lean`.

Assumed, not derived: that the poll of each round is formed from the previous tally in this way
(the walk is given by its properties, not computed), and no ties among the eligible tallies.
-/

namespace MemoryWalk

open LeaderRule StrategicInformation

variable {V A : Type}

/-- `x` is eligible at round `t`: the current leader, or a candidate that has not led up to `t`. -/
def Elig (L : ℕ → A) (t : ℕ) (x : A) : Prop := x = L t ∨ ∀ s, s ≤ t → L s ≠ x

/-- Round `t` is active: a candidate other than the leader is eligible. -/
def Active (L : ℕ → A) (t : ℕ) : Prop := ∃ y, y ≠ L t ∧ Elig L t y

/-- The walk with memory, given by its properties. -/
structure IsWalk [DecidableEq A] (P : V → A → Nat) (vs : List V) (L R : ℕ → A) : Prop where
  runner_ne : ∀ t, Active L t → R t ≠ L t
  runner_elig : ∀ t, Active L t → Elig L t (R t)
  leader_elig : ∀ t, Active L t → Elig L t (L (t + 1))
  leads : ∀ t, Active L t → LeadsIn P vs (Elig L t) (L t) (R t) (L (t + 1))
  second : ∀ t, Active L t → Active L (t + 1) → ∀ y, Elig L (t + 1) y → y ≠ L (t + 1) →
    y ≠ R (t + 1) → tally P vs (L t) (R t) y < tally P vs (L t) (R t) (R (t + 1))
  stop : ∀ t, ¬ Active L t → L (t + 1) = L t

/-- If the leader is kept, the eligible candidates stay the same. -/
theorem elig_succ {L : ℕ → A} {t : ℕ} (h : L (t + 1) = L t) (x : A) :
    Elig L (t + 1) x ↔ Elig L t x := by
  unfold Elig
  constructor
  · rintro (hx | hx)
    · exact Or.inl (hx.trans h)
    · exact Or.inr (fun s hs => hx s (by omega))
  · rintro (hx | hx)
    · exact Or.inl (hx.trans h.symm)
    · by_cases hxl : x = L t
      · exact Or.inl (hxl.trans h.symm)
      · refine Or.inr (fun s hs => ?_)
        rcases Nat.lt_or_ge s (t + 1) with hlt | hge
        · exact hx s (by omega)
        · have hst : s = t + 1 := by omega
          rw [hst, h]
          exact fun e => hxl e.symm

theorem active_succ {L : ℕ → A} {t : ℕ} (h : L (t + 1) = L t) :
    Active L (t + 1) ↔ Active L t := by
  unfold Active
  constructor
  · rintro ⟨y, hy, he⟩
    exact ⟨y, by rw [← h]; exact hy, (elig_succ h y).mp he⟩
  · rintro ⟨y, hy, he⟩
    exact ⟨y, by rw [h]; exact hy, (elig_succ h y).mpr he⟩

/-- Every change of leader brings a candidate that has not led before. -/
theorem hnew_walk [DecidableEq A] {P : V → A → Nat} {vs : List V} {L R : ℕ → A}
    (hw : IsWalk P vs L R) : ∀ t, L (t + 1) ≠ L t → L (t + 1) ∉ led L t := by
  intro t h hmem
  have hact : Active L t := by
    by_contra hna
    exact h (hw.stop t hna)
  rcases hw.leader_elig t hact with h' | h'
  · exact h h'
  · unfold led at hmem
    obtain ⟨s, hs, hsL⟩ := Finset.mem_image.mp hmem
    exact h' s (by have := Finset.mem_range.mp hs; omega) hsL

/-- A leader kept for two rounds is beaten by no eligible candidate. -/
theorem no_beater [DecidableEq A] {P : V → A → Nat} {vs : List V} {L R : ℕ → A}
    (hw : IsWalk P vs L R) (hs : LeaderRule.Strict P) {t : ℕ} (h1 : L (t + 1) = L t)
    (h2 : L (t + 1 + 1) = L t) : ∀ b, Elig L t b → b ≠ L t → ¬ beats P vs b (L t) := by
  intro b hb hbt hbeat
  have hact : Active L t := ⟨b, hbt, hb⟩
  have hact1 : Active L (t + 1) := (active_succ h1).mpr hact
  have hc1 : R (t + 1) ≠ L t := by
    have := hw.runner_ne (t + 1) hact1
    rwa [h1] at this
  have hsec : SecondIn P vs (Elig L t) (L t) (R t) (R (t + 1)) := by
    intro y hy hyl hyc
    exact hw.second t hact hact1 y ((elig_succ h1 y).mpr hy) (by rw [h1]; exact hyl) hyc
  have hfall := (beaten_leader_falls_in P hs vs hc1 hsec ⟨b, hb, hbt, hbeat⟩).2
  have hl := hw.leads (t + 1) hact1
  have hce : Elig L (t + 1) (R (t + 1)) := hw.runner_elig (t + 1) hact1
  have hlt := hl (R (t + 1)) hce (by rw [h2]; exact hc1)
  rw [h2, h1] at hlt
  omega

/-- A leader kept for two rounds is kept for good. -/
theorem hstay_walk [DecidableEq A] {P : V → A → Nat} {vs : List V} {L R : ℕ → A}
    (hw : IsWalk P vs L R) (hs : LeaderRule.Strict P)
    (hodd : ∀ x y, x ≠ y → pref P vs x y ≠ pref P vs y x) :
    ∀ t, L (t + 1) = L t → L (t + 1 + 1) = L t → ConstFrom L t := by
  intro t h1 h2
  have hnb := no_beater hw hs h1 h2
  have key : ∀ k, L (t + k) = L t ∧ ∀ x, Elig L (t + k) x ↔ Elig L t x := by
    intro k
    induction k with
    | zero => exact ⟨rfl, fun x => Iff.rfl⟩
    | succ k ih =>
      obtain ⟨hk, hek⟩ := ih
      have hnext : L (t + k + 1) = L t := by
        by_cases hact : Active L (t + k)
        · have hl := hw.leads (t + k) hact
          rw [hk] at hl
          have hR := hw.runner_elig (t + k) hact
          have hRne := hw.runner_ne (t + k) hact
          rw [hk] at hRne
          have hkeep : LeadsIn P vs (Elig L (t + k)) (L t) (R (t + k)) (L t) := by
            apply keeps_in P hs vs (Ne.symm hRne) hR
            intro y hy hyl
            have hyt := (hek y).mp hy
            have hnot := hnb y hyt hyl
            have hne := hodd (L t) y (Ne.symm hyl)
            unfold beats at hnot ⊢
            omega
          by_contra hne
          have hLe := hw.leader_elig (t + k) hact
          have ha := hkeep (L (t + k + 1)) hLe hne
          have hLt : Elig L (t + k) (L t) := by
            rw [← hk]
            exact Or.inl rfl
          have hb := hl (L t) hLt (Ne.symm hne)
          omega
        · have hst := hw.stop (t + k) hact
          rw [hst, hk]
      refine ⟨hnext, fun x => ?_⟩
      have he := elig_succ (L := L) (t := t + k) (hnext.trans hk.symm) x
      rw [show t + (k + 1) = t + k + 1 by omega]
      exact he.trans (hek x)
  intro m hm
  have hm' := (key (m - t)).1
  rwa [show t + (m - t) = m by omega] at hm'

/-- Once in a dominant set, the leader stays in it. -/
theorem hstayS_walk [DecidableEq A] {P : V → A → Nat} {vs : List V} {L R : ℕ → A}
    (hw : IsWalk P vs L R) (hs : LeaderRule.Strict P) (S : A → Prop) (hS : Dominant P vs S) :
    ∀ t, S (L t) → S (L (t + 1)) := by
  intro t ht
  by_cases h : L (t + 1) = L t
  · rw [h]
    exact ht
  · have hact : Active L t := by
      by_contra hna
      exact h (hw.stop t hna)
    have hb := new_leader_beats_in P hs vs (E := Elig L t) (Ne.symm (hw.runner_ne t hact))
      (Or.inl rfl) (hw.runner_elig t hact) h (hw.leads t hact)
    refine Classical.byContradiction (fun hn => ?_)
    have hb' := hS (L t) (L (t + 1)) ht hn
    unfold beats at hb hb'
    omega

/-- As long as no member of a non-empty dominant set has led, the leader changes within two
    rounds. -/
theorem hout_walk [DecidableEq A] {P : V → A → Nat} {vs : List V} {L R : ℕ → A}
    (hw : IsWalk P vs L R) (hs : LeaderRule.Strict P) (S : A → Prop) (hS : Dominant P vs S)
    (hne : ∃ s, S s) :
    ∀ t, (∀ s, s ≤ t → ¬ S (L s)) → L (t + 1) ≠ L t ∨ L (t + 1 + 1) ≠ L (t + 1) := by
  intro t hall
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2⟩ := hc
  obtain ⟨s0, hs0⟩ := hne
  have hnb := no_beater hw hs h1 (h2.trans h1)
  have helig : Elig L t s0 := Or.inr (fun r hr hrs => hall r hr (hrs ▸ hs0))
  have hs0t : s0 ≠ L t := fun e => hall t le_rfl (e ▸ hs0)
  exact hnb s0 helig hs0t (hS s0 (L t) hs0 (hall t le_rfl))

/-- Proposition 4, parts 4 and 5: the walk with memory settles by round `2 (|A| − 1)`, in every
    non-empty dominant set, so in the Smith set. -/
theorem memory_walk [Fintype A] [DecidableEq A] (P : V → A → Nat) (vs : List V) (L R : ℕ → A)
    (hw : IsWalk P vs L R) (hs : LeaderRule.Strict P)
    (hodd : ∀ x y, x ≠ y → pref P vs x y ≠ pref P vs y x)
    (S : A → Prop) (hS : Dominant P vs S) (hne : ∃ s, S s) :
    ConstFrom L (2 * (Fintype.card A - 1)) ∧ S (L (2 * (Fintype.card A - 1))) := by
  have hc := walk_settles L (hnew_walk hw) (hstay_walk hw hs hodd)
  exact ⟨hc, settled_in L S (hstayS_walk hw hs S hS) (hout_walk hw hs S hS hne) hc⟩

/-! ### Positions as utilities -/

/-- Distinct positions, read as utilities `−position`, differ by at least 1. -/
theorem one_le_gap {a b : ℕ} (h : a ≠ b) : (1 : ℝ) ≤ |(-(a : ℝ)) - (-(b : ℝ))| := by
  rcases Nat.lt_or_gt_of_ne h with hab | hab
  · have hab' : a + 1 ≤ b := hab
    have hc : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab'
    rw [abs_of_nonneg (show (0 : ℝ) ≤ -(a : ℝ) - -(b : ℝ) by linarith)]
    linarith
  · have hab' : b + 1 ≤ a := hab
    have hc : (b : ℝ) + 1 ≤ a := by exact_mod_cast hab'
    rw [abs_of_nonpos (show -(a : ℝ) - -(b : ℝ) ≤ 0 by linarith)]
    linarith

/-- In the finite corner with `2 δ D < 1`, the best approval ballot of a voter with positions
    `P i` is the leader-rule ballot of `LeaderRule.lean`. -/
theorem bridge_approval [Fintype A] [DecidableEq A] (P : V → A → Nat) (hs : LeaderRule.Strict P) (i : V)
    (p : A → A → ℝ) (hp0 : ∀ x y, 0 ≤ p x y) {D δ : ℝ}
    (hD : ∀ x y, |(-(P i x : ℝ)) - (-(P i y : ℝ))| ≤ D) (hδ : 0 ≤ δ) (hgap : 2 * δ * D < 1)
    {a1 a2 : A} (h12 : a1 ≠ a2) (hp12 : 0 < p a1 a2)
    (hw1 : ∑ y ∈ Finset.univ.erase a2, p a1 y ≤ δ * p a1 a2)
    (hpa : ∀ x, x ≠ a1 → 0 < p x a1)
    (hw : ∀ x, x ≠ a1 → ∑ y ∈ Finset.univ.erase a1, p x y ≤ δ * p x a1) (x : A) :
    approveR p (fun y => -(P i y : ℝ)) x = if approve P a1 a2 i x = true then 1 else 0 := by
  rw [prop6_approval p (fun y => -(P i y : ℝ)) hp0 hD
    (fun x y hxy => one_le_gap (hs i x y hxy)) hδ hgap h12 hp12 hw1 hpa hw x]
  unfold approve
  by_cases hx : x = a1 <;> simp [hx]

end MemoryWalk
