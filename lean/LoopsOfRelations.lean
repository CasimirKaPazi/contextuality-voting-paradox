import Mathlib

/-!
# Loops of relations

Propositions 1–3 of the working note *Loops of Relations*.

Simplification against the note: all variables take values in one type `V`
(each `V_i` is a subset of `V`, and a relation `R i` on `V_i × V_{i+1}` is a relation on `V`).
Contexts are indexed by natural numbers `i < n`; the context after `i` is `(i + 1) % n`.

* `Chain R m x y`: there is a path `x = f 0, f 1, …, f m = y` with `R i (f i) (f (i+1))`.
  For `m = n` this is the monodromy `M`.
* `Section R n`: an assignment of all variables around the loop (as a periodic function).
-/

namespace Loops

variable {V : Type*}

/-- A path of length `m` through the relations `R 0, …, R (m-1)`. -/
abbrev Chain (R : ℕ → V → V → Prop) (m : ℕ) (x y : V) : Prop :=
  ∃ f : ℕ → V, f 0 = x ∧ f m = y ∧ ∀ i < m, R i (f i) (f (i + 1))

/-- A global section of the loop of length `n`. -/
abbrev Section (R : ℕ → V → V → Prop) (n : ℕ) : Prop :=
  ∃ f : ℕ → V, (∀ i, f (i + n) = f i) ∧ ∀ i, R (i % n) (f i) (f (i + 1))

lemma chain_zero (R : ℕ → V → V → Prop) (x : V) : Chain R 0 x x :=
  ⟨fun _ => x, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩

lemma chain_snoc {R : ℕ → V → V → Prop} {m : ℕ} {x y z : V}
    (h : Chain R m x y) (hr : R m y z) : Chain R (m + 1) x z := by
  obtain ⟨f, h0, hm, hf⟩ := h
  refine ⟨fun i => if i ≤ m then f i else z, ?_, ?_, ?_⟩
  · simp [h0]
  · simp
  · intro i hi
    by_cases him : i < m
    · show R i (if i ≤ m then f i else z) (if i + 1 ≤ m then f (i + 1) else z)
      have h1 : i ≤ m := le_of_lt him
      have h2 : i + 1 ≤ m := him
      simp only [h1, h2, ↓reduceIte]
      exact hf i him
    · have hi' : i = m := by omega
      rw [hi']
      show R m (if m ≤ m then f m else z) (if m + 1 ≤ m then f (m + 1) else z)
      have h3 : ¬ (m + 1 ≤ m) := by omega
      simp only [le_refl m, h3, ↓reduceIte]
      rw [hm]
      exact hr

/-! ## Proposition 1 -/

/-- **Proposition 1(a).** Global sections correspond to fixed points of the monodromy. -/
theorem prop1a (R : ℕ → V → V → Prop) {n : ℕ} (hn : 0 < n) :
    Section R n ↔ ∃ x, Chain R n x x := by
  constructor
  · rintro ⟨f, hper, hR⟩
    refine ⟨f 0, f, rfl, ?_, ?_⟩
    · simpa using hper 0
    · intro i hi
      have := hR i
      rwa [Nat.mod_eq_of_lt hi] at this
  · rintro ⟨x, f, h0, hn', hf⟩
    refine ⟨fun i => f (i % n), ?_, ?_⟩
    · intro i; simp [Nat.add_mod_right]
    · intro i
      have hr : i % n < n := Nat.mod_lt i hn
      have hsucc : (i + 1) % n = (i % n + 1) % n := by
        rw [Nat.add_mod i 1 n, Nat.add_mod (i % n) 1 n, Nat.mod_mod]
      show R (i % n) (f (i % n)) (f ((i + 1) % n))
      rw [hsucc]
      by_cases hlt : i % n + 1 < n
      · rw [Nat.mod_eq_of_lt hlt]; exact hf _ hr
      · have heq : i % n + 1 = n := by omega
        have := hf _ hr
        rw [heq, hn', ← h0] at this
        rw [heq, Nat.mod_self]
        exact this

/-- A possibilistic model: context `i` allows the pairs `S i`; it is compatible when
consecutive contexts allow the same values to the variable they share. -/
abbrev Compatible (R : ℕ → V → V → Prop) (n : ℕ) (S : ℕ → V → V → Prop) : Prop :=
  (∀ i < n, ∃ a b, S i a b) ∧ (∀ i < n, ∀ a b, S i a b → R i a b) ∧
  ∀ i < n, ∀ v, (∃ a, S i a v) ↔ (∃ b, S ((i + 1) % n) v b)

/-- Non-empty value sets on which every relation is total in both directions. -/
abbrev GoodFamily (R : ℕ → V → V → Prop) (n : ℕ) (A : ℕ → Set V) : Prop :=
  (∀ i < n, (A i).Nonempty) ∧
  ∀ i < n, (∀ a ∈ A i, ∃ b ∈ A ((i + 1) % n), R i a b) ∧
           (∀ b ∈ A ((i + 1) % n), ∃ a ∈ A i, R i a b)

/-- **Proposition 1(b).** A compatible model exists exactly when a good family exists. -/
theorem prop1b (R : ℕ → V → V → Prop) {n : ℕ} (hn : 0 < n) :
    (∃ S, Compatible R n S) ↔ ∃ A, GoodFamily R n A := by
  unfold Compatible GoodFamily
  constructor
  · rintro ⟨S, hne, hsub, hcomp⟩
    refine ⟨fun i => {a | ∃ b, S i a b}, ?_, ?_⟩
    · intro i hi
      obtain ⟨a, b, h⟩ := hne i hi
      exact ⟨a, b, h⟩
    · intro i hi
      constructor
      · rintro a ⟨b, hab⟩
        exact ⟨b, (hcomp i hi b).mp ⟨a, hab⟩, hsub i hi a b hab⟩
      · intro b hb
        obtain ⟨a, hab⟩ := (hcomp i hi b).mpr hb
        exact ⟨a, ⟨b, hab⟩, hsub i hi a b hab⟩
  · rintro ⟨A, hne, htot⟩
    refine ⟨fun i a b => a ∈ A i ∧ b ∈ A ((i + 1) % n) ∧ R i a b, ?_, ?_, ?_⟩
    · intro i hi
      obtain ⟨a, ha⟩ := hne i hi
      obtain ⟨b, hb, hr⟩ := (htot i hi).1 a ha
      exact ⟨a, b, ha, hb, hr⟩
    · intro i _ a b h; exact h.2.2
    · intro i hi v
      have hj : (i + 1) % n < n := Nat.mod_lt _ hn
      constructor
      · rintro ⟨a, _, hv, _⟩
        obtain ⟨b, hb, hr⟩ := (htot _ hj).1 v hv
        exact ⟨b, hv, hb, hr⟩
      · rintro ⟨b, hv, _, _⟩
        obtain ⟨a, ha, hr⟩ := (htot i hi).2 v hv
        exact ⟨a, ha, hv, hr⟩

/-- Around the loop inside a good family: every point of `A 0` has a monodromy successor in `A 0`. -/
lemma around {R : ℕ → V → V → Prop} {n : ℕ} (_hn : 0 < n) {A : ℕ → Set V}
    (hA : GoodFamily R n A) (a : V) (ha : a ∈ A 0) :
    ∃ b ∈ A 0, Chain R n a b := by
  have key : ∀ m ≤ n, ∃ b ∈ A (m % n), Chain R m a b := by
    intro m
    induction m with
    | zero => intro _; exact ⟨a, by simpa using ha, chain_zero R a⟩
    | succ m ih =>
      intro hm
      obtain ⟨b, hb, hc⟩ := ih (by omega)
      have hmn : m < n := by omega
      rw [Nat.mod_eq_of_lt hmn] at hb
      obtain ⟨c, hc', hr⟩ := (hA.2 m hmn).1 b hb
      exact ⟨c, hc', chain_snoc hc hr⟩
  obtain ⟨b, hb, hc⟩ := key n le_rfl
  rw [Nat.mod_self] at hb
  exact ⟨b, hb, hc⟩

/-- On a finite set, a relation in which every point of a non-empty set `A` has a successor in `A`
has a cycle: some power has a fixed point (`TransGen M x x`). -/
lemma cycle_of_successor [Finite V] (M : V → V → Prop) (A : Set V) (hne : A.Nonempty)
    (hs : ∀ a ∈ A, ∃ b ∈ A, M a b) : ∃ x, Relation.TransGen M x x := by
  classical
  let succ : A → A := fun a => ⟨(hs a a.2).choose, (hs a a.2).choose_spec.1⟩
  have hM : ∀ a : A, M a (succ a) := fun a => (hs a a.2).choose_spec.2
  obtain ⟨a0, ha0⟩ := hne
  let s : ℕ → A := fun j => succ^[j] ⟨a0, ha0⟩
  have hstep : ∀ j, M (s j) (s (j + 1)) := by
    intro j
    have hs1 : s (j + 1) = succ (s j) := Function.iterate_succ_apply' succ j _
    rw [hs1]
    exact hM _
  have hchain : ∀ p d, Relation.TransGen M (s p) (s (p + d + 1)) := by
    intro p d
    induction d with
    | zero => exact Relation.TransGen.single (hstep p)
    | succ d ih =>
      have h := Relation.TransGen.tail ih (hstep (p + d + 1))
      rwa [show p + d + 1 + 1 = p + (d + 1) + 1 by omega] at h
  obtain ⟨p, q, hpq, heq⟩ := Finite.exists_ne_map_eq_of_infinite s
  rcases lt_or_gt_of_ne hpq with h | h
  · refine ⟨s p, ?_⟩
    have := hchain p (q - p - 1)
    rwa [show p + (q - p - 1) + 1 = q by omega, ← heq] at this
  · refine ⟨s q, ?_⟩
    have := hchain q (p - q - 1)
    rwa [show q + (p - q - 1) + 1 = p by omega, heq] at this

/-- **Proposition 1(c).** On a finite value set, a compatible model gives a fixed point of some
power of the monodromy (a global section of a finite cover). -/
theorem prop1c [Finite V] (R : ℕ → V → V → Prop) {n : ℕ} (hn : 0 < n)
    (h : ∃ S, Compatible R n S) : ∃ x, Relation.TransGen (Chain R n) x x := by
  obtain ⟨A, hA⟩ := (prop1b R hn).mp h
  exact cycle_of_successor _ (A 0) (hA.1 0 hn) (fun a ha => around hn hA a ha)

/-! ## Proposition 2: edges given by a group -/

section Group

variable {G : Type*} [Group G] [MulAction G V]

/-- Context `i` allows the moves in `Γ i`. -/
abbrev GRel (Γ : ℕ → Set G) : ℕ → V → V → Prop := fun i v w => ∃ g ∈ Γ i, w = g • v

/-- Partial products `c (i-1) * ⋯ * c 0`. -/
def prodUpTo (c : ℕ → G) : ℕ → G
  | 0 => 1
  | i + 1 => c i * prodUpTo c i

/-- The holonomy set `Γ (n-1) ⋯ Γ 0`. -/
def Holonomy (Γ : ℕ → Set G) (n : ℕ) : Set G :=
  {h | ∃ c : ℕ → G, (∀ i < n, c i ∈ Γ i) ∧ h = prodUpTo c n}

lemma chain_group (Γ : ℕ → Set G) (n : ℕ) (x y : V) :
    Chain (GRel Γ) n x y ↔ ∃ h ∈ Holonomy Γ n, y = h • x := by
  classical
  constructor
  · rintro ⟨f, h0, hn, hf⟩
    let c : ℕ → G := fun i => if hi : i < n then (hf i hi).choose else 1
    have hc : ∀ i (hi : i < n), c i ∈ Γ i ∧ f (i + 1) = c i • f i := by
      intro i hi
      have hci : c i = (hf i hi).choose := by simp [c, hi]
      rw [hci]
      exact (hf i hi).choose_spec
    have hpath : ∀ i ≤ n, f i = prodUpTo c i • x := by
      intro i
      induction i with
      | zero => intro _; simp [prodUpTo, h0]
      | succ i ih =>
        intro hi
        rw [(hc i (by omega)).2, ih (by omega)]
        show c i • (prodUpTo c i • x) = (c i * prodUpTo c i) • x
        rw [mul_smul]
    exact ⟨prodUpTo c n, ⟨c, fun i hi => (hc i hi).1, rfl⟩, by rw [← hn, hpath n le_rfl]⟩
  · rintro ⟨h, ⟨c, hc, rfl⟩, rfl⟩
    refine ⟨fun i => prodUpTo c i • x, by simp [prodUpTo], rfl, ?_⟩
    intro i hi
    refine ⟨c i, hc i hi, ?_⟩
    show (c i * prodUpTo c i) • x = c i • (prodUpTo c i • x)
    rw [mul_smul]

/-- **Proposition 2, first part.** For a free action, the loop has a global section exactly when
the identity lies in the holonomy set. -/
theorem prop2_section [Nonempty V] (hfree : ∀ (g : G) (x : V), g • x = x → g = 1)
    (Γ : ℕ → Set G) {n : ℕ} (hn : 0 < n) :
    Section (GRel (V := V) Γ) n ↔ (1 : G) ∈ Holonomy Γ n := by
  rw [prop1a _ hn]
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨h, hH, hxh⟩ := (chain_group Γ n x x).mp hx
    rwa [hfree h x hxh.symm] at hH
  · intro h1
    obtain ⟨x⟩ := ‹Nonempty V›
    exact ⟨x, (chain_group Γ n x x).mpr ⟨1, h1, (one_smul G x).symm⟩⟩

lemma prodUpTo_periodic (c : ℕ → G) (n : ℕ) (hc : ∀ i, c (i + n) = c i) :
    ∀ j, prodUpTo c (n + j) = prodUpTo c j * prodUpTo c n := by
  intro j
  induction j with
  | zero => simp [prodUpTo]
  | succ j ih =>
    rw [← Nat.add_assoc]
    show c (n + j) * prodUpTo c (n + j) = c j * prodUpTo c j * prodUpTo c n
    rw [ih, mul_assoc, Nat.add_comm n j, hc j]

lemma prodUpTo_mul (c : ℕ → G) (n : ℕ) (hc : ∀ i, c (i + n) = c i) :
    ∀ k, prodUpTo c (k * n) = prodUpTo c n ^ k := by
  intro k
  induction k with
  | zero => simp [prodUpTo]
  | succ k ih =>
    rw [Nat.add_mul, one_mul, Nat.add_comm, prodUpTo_periodic c n hc, ih, pow_succ]

/-- **Proposition 2, second part.** Single moves `c i` repeating with period `n`, holonomy
`h = c (n-1) ⋯ c 0`, free action: the loop run `k` times has a global section exactly when
`h ^ k = 1`, i.e. when the order of `h` divides `k`. So `h = 1` gives a section, `h` of finite
order `k` a section on the `k`-fold cover only, and `h` of infinite order none on any finite cover. -/
theorem prop2_cover [Nonempty V] (hfree : ∀ (g : G) (x : V), g • x = x → g = 1)
    (c : ℕ → G) {n : ℕ} (hn : 0 < n) (hc : ∀ i, c (i + n) = c i) {k : ℕ} (hk : 0 < k) :
    Section (GRel (V := V) (fun i => ({c i} : Set G))) (k * n) ↔ orderOf (prodUpTo c n) ∣ k := by
  rw [orderOf_dvd_iff_pow_eq_one, prop2_section hfree _ (Nat.mul_pos hk hn)]
  constructor
  · rintro ⟨c', hc', heq⟩
    have : ∀ i < k * n, c' i = c i := fun i hi => hc' i hi
    have hsame : ∀ i ≤ k * n, prodUpTo c' i = prodUpTo c i := by
      intro i
      induction i with
      | zero => intro _; rfl
      | succ i ih => intro hi; simp only [prodUpTo]; rw [this i (by omega), ih (by omega)]
    rw [heq, hsame _ le_rfl, prodUpTo_mul c n hc]
  · intro h
    exact ⟨c, fun i _ => rfl, by rw [prodUpTo_mul c n hc, h]⟩

end Group

/-! ## Proposition 3: an edge chosen by an adversary -/

/-- **Proposition 3.** `BR c b`: `b` is a best reply to `c`. The opponents may answer `b` with any
`c` allowed by `A b` (never empty). They have an answer function inside `A` without fixed point
(no `b` is a best reply to the answer to `b`) exactly when no `b` is a universal fixed point
(a best reply to every allowed answer). With `A` everything this is the diagonal lemma; with `A`
the opponent's best replies it is the rational diagonal (no strict Nash strategy). -/
theorem prop3 {B C : Type*} (BR : C → B → Prop) (A : B → C → Prop) :
    (∃ f : B → C, (∀ b, A b (f b)) ∧ ∀ b, ¬ BR (f b) b) ↔
      (∀ b, ∃ c, A b c) ∧ ¬ ∃ b, ∀ c, A b c → BR c b := by
  constructor
  · rintro ⟨f, hA, hno⟩
    refine ⟨fun b => ⟨f b, hA b⟩, ?_⟩
    rintro ⟨b, hb⟩
    exact hno b (hb _ (hA b))
  · rintro ⟨hne, hno⟩
    have : ∀ b, ∃ c, A b c ∧ ¬ BR c b := by
      intro b
      by_contra h
      exact hno ⟨b, fun c hc => by_contra fun hbr => h ⟨c, hc, hbr⟩⟩
    choose f hf using this
    exact ⟨f, fun b => (hf b).1, fun b => (hf b).2⟩

end Loops
