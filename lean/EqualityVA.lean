/-
  Propositions 1 and 2 of *Equality of Voters and Alternatives*
  (`notes/equality-of-voters-and-alternatives.md`, Section 1).

  Setting. Candidates are `Fin m`. A ballot is a list of candidates, best
  first; it is a strict ranking (`ValidB`) when it has no repetition and
  length `m`. A profile is a multiset of ballots, so rules are anonymous by
  construction; `ValidP` asks every ballot to be a strict ranking. A rule
  gives a number to every candidate at every profile; `Lottery` asks these to
  sum to one at strict profiles.

  * `pair b`: the ballot `b` with its reverse. A profile is *balanced*
    (`Balanced`) when it is a sum of such pairs.
  * `ECV`: the Equality Criterion, here equality of voters: adding a ballot
    and its reverse to a strict profile never changes the lottery.
  * `Neutral`: renaming the candidates by `τ` renames the lottery.
  * `IndepClones`: independence of clones for a pair of clones. A ballot on
    `m + 1` candidates clones candidate `x` of `m` with the new candidate
    `Fin.last m` when the two are adjacent in it (`IsClone`); merging them
    (`unclone`) gives a ballot on `m` candidates. At a profile of such
    ballots, every other candidate keeps its probability and the two clones
    together get the probability of `x`. Asking this only for pairs of clones
    makes the hypothesis weaker than independence of clones, and so the
    impossibility stronger.

  Results.
  * `prop1`: a neutral lottery rule satisfying EC-V gives the uniform lottery
    `1/m` at every balanced profile. All balanced profiles have one lottery
    (`balanced_eq`), a renaming of a balanced profile is balanced, so the
    lottery is fixed by every renaming.
  * `prop2`: no family of rules, one for each number of candidates, is
    neutral, a lottery, EC-V and independent of clones. Only two and three
    candidates are used (`prop2_sizes`): {ab, ba} gives a one half, its clone
    {a a′ b, b a′ a} gives a, a′ and b one third each.

  Not here: Propositions 3 to 20.
-/

module

public import Mathlib

@[expose] public section

namespace EqualityVA

open Finset

/-! ### Ballots, profiles, rules -/

/-- A strict ranking of the candidates `Fin m`, best first. -/
def ValidB {m : ℕ} (b : List (Fin m)) : Prop := b.Nodup ∧ b.length = m

instance {m : ℕ} (b : List (Fin m)) : Decidable (ValidB b) := by
  unfold ValidB; infer_instance

/-- A profile of strict rankings. -/
def ValidP {m : ℕ} (p : Multiset (List (Fin m))) : Prop := ∀ b ∈ p, ValidB b

/-- A ballot together with its reverse. -/
def pair {m : ℕ} (b : List (Fin m)) : Multiset (List (Fin m)) := ↑[b, b.reverse]

/-- A rule for `m` candidates. -/
abbrev Rule (m : ℕ) := Multiset (List (Fin m)) → Fin m → ℝ

/-- The numbers sum to one at every strict profile. -/
def Lottery {m : ℕ} (L : Rule m) : Prop := ∀ p, ValidP p → ∑ x, L p x = 1

/-- Equality of voters (the Equality Criterion). -/
def ECV {m : ℕ} (L : Rule m) : Prop :=
  ∀ p b, ValidP p → ValidB b → L (p + pair b) = L p

/-- Neutrality: renaming the candidates renames the lottery. -/
def Neutral {m : ℕ} (L : Rule m) : Prop :=
  ∀ (τ : Equiv.Perm (Fin m)) p, ValidP p → ∀ x, L (p.map (List.map τ)) (τ x) = L p x

/-- A sum of pairs of a strict ranking and its reverse. -/
def Balanced {m : ℕ} (p : Multiset (List (Fin m))) : Prop :=
  ∃ bs : List (List (Fin m)), (∀ b ∈ bs, ValidB b) ∧ p = (bs.map pair).sum

/-! ### Clones -/

/-- Merge the new candidate `Fin.last m` into `x`. -/
def merge {m : ℕ} (x : Fin m) (y : Fin (m + 1)) : Fin m :=
  if h : (y : ℕ) < m then ⟨y, h⟩ else x

/-- Remove adjacent repetitions. -/
def squash {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: l =>
    match l with
    | [] => [a]
    | b :: _ => if a = b then squash l else a :: squash l

/-- The ballot with the two clones merged into `x`. -/
def unclone {m : ℕ} (x : Fin m) (b : List (Fin (m + 1))) : List (Fin m) :=
  squash (b.map (merge x))

/-- In a strict ranking of `m + 1` candidates, `x` and `Fin.last m` are
    adjacent exactly when merging them leaves `m` entries. -/
def IsClone {m : ℕ} (x : Fin m) (b : List (Fin (m + 1))) : Prop := (unclone x b).length = m

instance {m : ℕ} (x : Fin m) (b : List (Fin (m + 1))) : Decidable (IsClone x b) := by
  unfold IsClone; infer_instance

/-- Independence of clones, for a pair of clones `x` and `Fin.last m`. -/
def IndepClones (L : ∀ m, Rule m) : Prop :=
  ∀ m (x : Fin m) (p : Multiset (List (Fin (m + 1)))), ValidP p → (∀ b ∈ p, IsClone x b) →
    (∀ y : Fin m, y ≠ x → L (m + 1) p (Fin.castSucc y) = L m (p.map (unclone x)) y) ∧
    L (m + 1) p (Fin.castSucc x) + L (m + 1) p (Fin.last m) = L m (p.map (unclone x)) x

/-! ### Balanced profiles -/

variable {m : ℕ}

lemma validB_reverse {b : List (Fin m)} (h : ValidB b) : ValidB b.reverse :=
  ⟨List.nodup_reverse.mpr h.1, by rw [List.length_reverse]; exact h.2⟩

lemma validB_map (τ : Equiv.Perm (Fin m)) {b : List (Fin m)} (h : ValidB b) :
    ValidB (b.map τ) :=
  ⟨h.1.map τ.injective, by rw [List.length_map]; exact h.2⟩

lemma mem_pair {b c : List (Fin m)} : c ∈ pair b ↔ c = b ∨ c = b.reverse := by
  simp [pair]

lemma validP_add {p q : Multiset (List (Fin m))} (hp : ValidP p) (hq : ValidP q) :
    ValidP (p + q) := fun b hb => by
  rcases Multiset.mem_add.mp hb with h | h
  · exact hp b h
  · exact hq b h

lemma validP_pairs {bs : List (List (Fin m))} (h : ∀ b ∈ bs, ValidB b) :
    ValidP (bs.map pair).sum := by
  induction bs with
  | nil => intro b hb; simp at hb
  | cons b bs ih =>
    rw [List.map_cons, List.sum_cons]
    refine validP_add (fun c hc => ?_) (ih fun c hc => h c (List.mem_cons_of_mem b hc))
    rcases mem_pair.mp hc with rfl | rfl
    · exact h c (by simp)
    · exact validB_reverse (h b (by simp))

lemma validP_balanced {p : Multiset (List (Fin m))} (hp : Balanced p) : ValidP p := by
  obtain ⟨bs, hbs, rfl⟩ := hp
  exact validP_pairs hbs

/-- Adding pairs one at a time. -/
lemma add_pairs {L : Rule m} (hL : ECV L) {p : Multiset (List (Fin m))} (hp : ValidP p) :
    ∀ {bs : List (List (Fin m))}, (∀ b ∈ bs, ValidB b) → L (p + (bs.map pair).sum) = L p
  | [], _ => by simp
  | b :: bs, h => by
    have hbs : ∀ c ∈ bs, ValidB c := fun c hc => h c (List.mem_cons_of_mem b hc)
    rw [List.map_cons, List.sum_cons, add_left_comm, add_comm]
    rw [hL _ b (validP_add hp (validP_pairs hbs)) (h b (by simp))]
    exact add_pairs hL hp hbs

/-- All balanced profiles have the same lottery. -/
theorem balanced_eq {L : Rule m} (hL : ECV L) {p q : Multiset (List (Fin m))}
    (hp : Balanced p) (hq : Balanced q) : L p = L q := by
  obtain ⟨bs, hbs, rfl⟩ := hp
  obtain ⟨cs, hcs, rfl⟩ := hq
  rw [← add_pairs hL (validP_pairs hbs) hcs, ← add_pairs hL (validP_pairs hcs) hbs, add_comm]

lemma map_pairs (τ : Equiv.Perm (Fin m)) (bs : List (List (Fin m))) :
    (bs.map pair).sum.map (List.map τ) = ((bs.map (List.map τ)).map pair).sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.map_cons, List.sum_cons, Multiset.map_add, ih, List.map_cons, List.map_cons,
      List.sum_cons]
    congr 1
    simp [pair]

lemma balanced_map (τ : Equiv.Perm (Fin m)) {p : Multiset (List (Fin m))} (hp : Balanced p) :
    Balanced (p.map (List.map τ)) := by
  obtain ⟨bs, hbs, rfl⟩ := hp
  refine ⟨bs.map (List.map τ), fun c hc => ?_, map_pairs τ bs⟩
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hc
  exact validB_map τ (hbs b hb)

/-- **Proposition 1.** A neutral lottery rule satisfying EC-V gives the uniform
    lottery at every balanced profile. -/
theorem prop1 {L : Rule m} (hlot : Lottery L) (hn : Neutral L) (hL : ECV L)
    {p : Multiset (List (Fin m))} (hp : Balanced p) (x : Fin m) : L p x = 1 / m := by
  have hv := validP_balanced hp
  -- the lottery is fixed by every renaming
  have hfix : ∀ (τ : Equiv.Perm (Fin m)) y, L p (τ y) = L p y := fun τ y => by
    have h := hn τ p hv y
    rwa [balanced_eq hL (balanced_map τ hp) hp] at h
  have hconst : ∀ y, L p y = L p x := fun y => by
    have := hfix (Equiv.swap x y) x
    rwa [Equiv.swap_apply_left] at this
  have hsum := hlot p hv
  rw [Finset.sum_congr rfl (fun y _ => hconst y), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr x.pos.ne'
  rw [eq_div_iff hm, mul_comm]
  exact hsum

/-! ### Proposition 2 -/

/-- {ab, ba} on two candidates. -/
def p₂ : Multiset (List (Fin 2)) := pair [0, 1]

/-- {a a′ b, b a′ a} on three candidates, a = 0, b = 1, a′ = 2 = `Fin.last 2`. -/
def p₃ : Multiset (List (Fin 3)) := pair [0, 2, 1]

lemma balanced_p₂ : Balanced p₂ := ⟨[[0, 1]], by decide, by simp [p₂]⟩

lemma balanced_p₃ : Balanced p₃ := ⟨[[0, 2, 1]], by decide, by simp [p₃]⟩

lemma clone_p₃ : ∀ b ∈ p₃, IsClone (0 : Fin 2) b := by
  intro b hb
  rw [p₃, mem_pair] at hb
  rcases hb with rfl | rfl <;> decide

lemma unclone_p₃ : p₃.map (unclone (0 : Fin 2)) = p₂ := by decide

/-- **Proposition 2, with two and three candidates.** -/
theorem prop2_sizes (L₂ : Rule 2) (L₃ : Rule 3) (hlot₂ : Lottery L₂) (hlot₃ : Lottery L₃)
    (hn₂ : Neutral L₂) (hn₃ : Neutral L₃) (hL₂ : ECV L₂) (hL₃ : ECV L₃)
    (hc : L₃ p₃ (Fin.castSucc 0) + L₃ p₃ (Fin.last 2) = L₂ (p₃.map (unclone 0)) 0) : False := by
  rw [unclone_p₃, prop1 hlot₂ hn₂ hL₂ balanced_p₂, prop1 hlot₃ hn₃ hL₃ balanced_p₃,
    prop1 hlot₃ hn₃ hL₃ balanced_p₃] at hc
  norm_num at hc

/-- **Proposition 2.** No neutral lottery rule, defined for every number of
    candidates, satisfies EC-V and independence of clones. -/
theorem prop2 (L : ∀ m, Rule m) (hlot : ∀ m, 0 < m → Lottery (L m)) (hn : ∀ m, Neutral (L m))
    (hL : ∀ m, ECV (L m)) (hic : IndepClones L) : False :=
  prop2_sizes (L 2) (L 3) (hlot 2 (by norm_num)) (hlot 3 (by norm_num)) (hn 2) (hn 3) (hL 2) (hL 3)
    (hic 2 0 p₃ (validP_balanced balanced_p₃) clone_p₃).2

end EqualityVA
