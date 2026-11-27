/-
  Theorems A and B of *A tight form without a rational diagonal*
  (`notes/tight-form-without-rational-diagonal.md`, Section 5), Proposition 5‴
  of *Walls and Strategy*: the exact criterion for two-player forms with three
  outcomes.

  Setting (`Veto3`): outcomes a, b, c, distinct, and nothing else; a row that
  is constant c and a column that is constant c (the common veto); a and b
  occur. Rows are player 1's strategies; the sets of rows and columns need not
  be finite. Strict preferences are injective utilities in ℕ, as in
  `NonTight.lean` and `TwoPlayer.lean`.

  * `Wall`: a row all of whose c-cells lie in columns that are constant c.
  * `CondA g c x`: some row inside {x, c} has its c-cells in columns without x.
  * `CondE g c x y`: some row holding y has its y-cells in columns without x,
    or some wall row does not hold y.
  * `thmB`: player 1 has no rational diagonal exactly when there is a wall
    row and (A_a), (A_b), (E_ab), (E_ba) hold. With `rd2_iff` the same
    criterion read on columns decides player 2.

  The proof follows the note. Sufficiency goes through player 1's orders:
  with c on top the constant row is a best reply to everything
  (`sn_ctop`); with c in the middle the row of (A_x) is (`sn_cmid`); with c
  at the bottom the row depends on player 2's order (`sn_cbot`). Necessity
  reads off a wall row, the row of (A_x) and the row of (E_xy) from the
  strict Nash strategies under three particular pairs of orders
  (`wall_nec`, `condA_nec`, `condE_nec`), built from `ord3`, the utility
  with values 2, 1, 0. The roles of a and b are exchanged by `Veto3.swap`.

  * `thmA`, Theorem A: on a non-dictatorial form with three outcomes, all
    occurring, and no outcome forced by both players, some player has a
    rational diagonal. One of three configurations works (`thmA_core`):
    (1, (t, u, v), reverse), (1, (t, v, u), reverse) and (2, (u, t, v),
    rotation), where player 2 forces nothing and player 1 does not force t
    (`works_rev`, `works_rot`); otherwise the players are exchanged.

  Together they give Proposition 5‴: a non-dictatorial form with three
  outcomes, all occurring, without a rational diagonal for either player has
  a common veto (`veto_of_no_diagonal`), and with a common veto neither
  player has one exactly when both satisfy the criterion (`prop5`).
-/

module

public import Mathlib
public import TwoPlayer

@[expose] public section

namespace ThreeOutcomes

open NonTight TwoPlayer

variable {A B X : Type}

/-- Three outcomes a, b, c with a common veto c, and a, b occurring. -/
structure Veto3 (g : A → B → X) (a b c : X) : Prop where
  ab : a ≠ b
  ac : a ≠ c
  bc : b ≠ c
  cover : ∀ t, t = a ∨ t = b ∨ t = c
  row : ∃ r, ∀ s, g r s = c
  col : ∃ s, ∀ r, g r s = c
  onto_a : ∃ r s, g r s = a
  onto_b : ∃ r s, g r s = b

/-- Exchanging the roles of a and b. -/
theorem Veto3.swap {g : A → B → X} {a b c : X} (h : Veto3 g a b c) : Veto3 g b a c :=
  ⟨h.ab.symm, h.bc, h.ac, fun t => by rcases h.cover t with e | e | e <;> tauto,
    h.row, h.col, h.onto_b, h.onto_a⟩

/-- A wall row: all its c-cells lie in columns that are constant c. -/
def Wall (g : A → B → X) (c : X) (r : A) : Prop := ∀ s, g r s = c → ∀ r', g r' s = c

/-- (A_x): some row inside {x, c} has its c-cells in columns without x. -/
def CondA (g : A → B → X) (c x : X) : Prop :=
  ∃ r, (∀ s, g r s = x ∨ g r s = c) ∧ ∀ s, g r s = c → ∀ r', g r' s ≠ x

/-- (E_xy): some row holding y has its y-cells in columns without x, or some
    wall row does not hold y. -/
def CondE (g : A → B → X) (c x y : X) : Prop :=
  (∃ r, (∃ s, g r s = y) ∧ ∀ s, g r s = y → ∀ r', g r' s ≠ x) ∨
    ∃ r, Wall g c r ∧ ∀ s, g r s ≠ y

/-- The criterion of Theorem B for player 1. -/
def Criterion (g : A → B → X) (a b c : X) : Prop :=
  (∃ r, Wall g c r) ∧ CondA g c a ∧ CondA g c b ∧ CondE g c a b ∧ CondE g c b a

/-- If z occurs in row r and player 2 prefers it to every other outcome of the
    row, the best replies of player 2 to r are the z-cells. -/
lemma br2_iff_of_top {g : A → B → X} {v : X → ℕ} {r : A} {z : X} (hz : ∃ s, g r s = z)
    (htop : ∀ s, g r s ≠ z → v (g r s) < v z) (s : B) : BR2 g v r s ↔ g r s = z := by
  constructor
  · intro hb
    by_contra hne
    obtain ⟨s', hs'⟩ := hz
    have h1 := hb s'
    rw [hs'] at h1
    have h2 := htop s hne
    omega
  · intro he s'
    rw [he]
    by_cases h' : g r s' = z
    · rw [h']
    · exact (htop s' h').le

/-! ### Sufficiency -/

/-- c on top: the constant row is a best reply to every column. -/
lemma sn_ctop {g : A → B → X} {x y c : X} (h : Veto3 g x y c) (u v : X → ℕ)
    (hu : u x < u c ∧ u y < u c) : ∃ r, StrictNash1 g u v r := by
  obtain ⟨r, hr⟩ := h.row
  refine ⟨r, fun s _ r' => ?_⟩
  show u (g r' s) ≤ u (g r s)
  rw [hr s]
  rcases h.cover (g r' s) with e | e | e <;> rw [e] <;> omega

/-- P = (x, c, y): the row of (A_x) is a best reply to every column. -/
lemma sn_cmid {g : A → B → X} {x y c : X} (h : Veto3 g x y c) (u v : X → ℕ)
    (hu : u y < u c ∧ u c < u x) (hA : CondA g c x) : ∃ r, StrictNash1 g u v r := by
  obtain ⟨r, hr, hrc⟩ := hA
  refine ⟨r, fun s _ r' => ?_⟩
  show u (g r' s) ≤ u (g r s)
  rcases hr s with e | e
  · rw [e]
    rcases h.cover (g r' s) with e' | e' | e' <;> rw [e'] <;> omega
  · have hne := hrc s e r'
    rw [e]
    rcases h.cover (g r' s) with e' | e' | e'
    · exact absurd e' hne
    · rw [e']
      omega
    · rw [e']

/-- P = (x, y, c): a strict Nash strategy for each order of player 2. -/
lemma sn_cbot {g : A → B → X} {x y c : X} (h : Veto3 g x y c) (u v : X → ℕ)
    (hu : u c < u y ∧ u y < u x) (hv : Injective v) (hW : ∃ r, Wall g c r)
    (hA : CondA g c x) (hE : CondE g c x y) : ∃ r, StrictNash1 g u v r := by
  have h1 : v x ≠ v y := fun e => h.ab (hv _ _ e)
  have h2 : v x ≠ v c := fun e => h.ac (hv _ _ e)
  have h3 : v y ≠ v c := fun e => h.bc (hv _ _ e)
  obtain ⟨s0, hs0⟩ := h.col
  -- an x-cell is a best reply of player 1
  have topx : ∀ r s, g r s = x → BR1 g u r s := by
    intro r s e r'
    show u (g r' s) ≤ u (g r s)
    rw [e]
    rcases h.cover (g r' s) with e' | e' | e' <;> rw [e'] <;> omega
  by_cases hx : v y < v x ∧ v c < v x
  · -- player 2 prefers x: a row holding x
    obtain ⟨r, s1, hs1⟩ := h.onto_a
    have htop : ∀ s', g r s' ≠ x → v (g r s') < v x := by
      intro s' hne
      rcases h.cover (g r s') with e | e | e
      · exact absurd e hne
      · rw [e]; omega
      · rw [e]; omega
    exact ⟨r, fun s hb => topx r s ((br2_iff_of_top ⟨s1, hs1⟩ htop s).mp hb)⟩
  by_cases hc : v x < v c ∧ v y < v c
  · -- player 2 prefers c: a wall row
    obtain ⟨r, hr⟩ := hW
    have htop : ∀ s', g r s' ≠ c → v (g r s') < v c := by
      intro s' hne
      rcases h.cover (g r s') with e | e | e
      · rw [e]; omega
      · rw [e]; omega
      · exact absurd e hne
    refine ⟨r, fun s hb r' => ?_⟩
    have e := (br2_iff_of_top ⟨s0, hs0 r⟩ htop s).mp hb
    show u (g r' s) ≤ u (g r s)
    rw [hr s e r', e]
  have hy : v x < v y ∧ v c < v y := by omega
  by_cases hxc : v c < v x
  · -- Q = (y, x, c): the row of (A_x), whose favourite is x
    obtain ⟨r, hr, hrc⟩ := hA
    have hrx : ∃ s, g r s = x := by
      obtain ⟨r1, s1, hs1⟩ := h.onto_a
      rcases hr s1 with e | e
      · exact ⟨s1, e⟩
      · exact absurd hs1 (hrc s1 e r1)
    have htop : ∀ s', g r s' ≠ x → v (g r s') < v x := by
      intro s' hne
      rcases hr s' with e | e
      · exact absurd e hne
      · rw [e]; omega
    exact ⟨r, fun s hb => topx r s ((br2_iff_of_top hrx htop s).mp hb)⟩
  · -- Q = (y, c, x): the row of (E_xy)
    rcases hE with ⟨r, hry, hrx⟩ | ⟨r, hwall, hry⟩
    · have htop : ∀ s', g r s' ≠ y → v (g r s') < v y := by
        intro s' hne
        rcases h.cover (g r s') with e | e | e
        · rw [e]; omega
        · exact absurd e hne
        · rw [e]; omega
      refine ⟨r, fun s hb r' => ?_⟩
      have e := (br2_iff_of_top hry htop s).mp hb
      have hne := hrx s e r'
      show u (g r' s) ≤ u (g r s)
      rw [e]
      rcases h.cover (g r' s) with e' | e' | e'
      · exact absurd e' hne
      · rw [e']
      · rw [e']
        omega
    · have htop : ∀ s', g r s' ≠ c → v (g r s') < v c := by
        intro s' hne
        rcases h.cover (g r s') with e | e | e
        · rw [e]; omega
        · exact absurd e (hry s')
        · exact absurd e hne
      refine ⟨r, fun s hb r' => ?_⟩
      have e := (br2_iff_of_top ⟨s0, hs0 r⟩ htop s).mp hb
      show u (g r' s) ≤ u (g r s)
      rw [hwall s e r', e]

/-- **Theorem B, sufficiency.** -/
theorem criterion_suff {g : A → B → X} {a b c : X} (h : Veto3 g a b c)
    (hC : Criterion g a b c) : ¬ RationalDiagonal1 g := by
  rw [not_rd1_iff]
  intro u v hu hv
  obtain ⟨hW, hAa, hAb, hEab, hEba⟩ := hC
  have d1 : u a ≠ u b := fun e => h.ab (hu _ _ e)
  have d2 : u a ≠ u c := fun e => h.ac (hu _ _ e)
  have d3 : u b ≠ u c := fun e => h.bc (hu _ _ e)
  by_cases hct : u a < u c ∧ u b < u c
  · exact sn_ctop h u v hct
  by_cases hcb : u c < u a ∧ u c < u b
  · by_cases hab : u b < u a
    · exact sn_cbot h u v ⟨hcb.2, hab⟩ hv hW hAa hEab
    · exact sn_cbot h.swap u v ⟨hcb.1, by omega⟩ hv hW hAb hEba
  · by_cases hm : u b < u c
    · exact sn_cmid h u v ⟨hm, by omega⟩ hAa
    · exact sn_cmid h.swap u v ⟨by omega, by omega⟩ hAb

/-! ### Necessity -/

section Necessity

variable [DecidableEq X]

/-- The utility with values 2, 1, 0 on p, q, z; the third argument only names the worst outcome. -/
def ord3 (p q _z : X) (t : X) : ℕ := if t = p then 2 else if t = q then 1 else 0

lemma ord3_val {p q z : X} (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z) :
    ord3 p q z p = 2 ∧ ord3 p q z q = 1 ∧ ord3 p q z z = 0 :=
  ⟨by simp [ord3], by simp [ord3, hpq.symm], by simp [ord3, hpz.symm, hqz.symm]⟩

lemma ord3_cases {p q z : X} (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z)
    (hcov : ∀ t, t = p ∨ t = q ∨ t = z) (t : X) :
    (t = p ∧ ord3 p q z t = 2) ∨ (t = q ∧ ord3 p q z t = 1) ∨ (t = z ∧ ord3 p q z t = 0) := by
  have hv := ord3_val hpq hpz hqz
  rcases hcov t with e | e | e
  · exact Or.inl ⟨e, by rw [e]; exact hv.1⟩
  · exact Or.inr (Or.inl ⟨e, by rw [e]; exact hv.2.1⟩)
  · exact Or.inr (Or.inr ⟨e, by rw [e]; exact hv.2.2⟩)

lemma ord3_inj {p q z : X} (hpq : p ≠ q) (hpz : p ≠ z) (hqz : q ≠ z)
    (hcov : ∀ t, t = p ∨ t = q ∨ t = z) : Injective (ord3 p q z) := by
  intro t t' h
  rcases ord3_cases hpq hpz hqz hcov t with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩ <;>
    rcases ord3_cases hpq hpz hqz hcov t' with ⟨e', hv'⟩ | ⟨e', hv'⟩ | ⟨e', hv'⟩ <;>
    first | omega | rw [e, e']

/-- Under P = (x, y, c) and Q = (c, x, y), a strict Nash row is a wall row. -/
lemma wall_nec {g : A → B → X} {x y c : X} (h : Veto3 g x y c)
    (hN : ∀ u v : X → ℕ, Injective u → Injective v → ∃ r, StrictNash1 g u v r) :
    ∃ r, Wall g c r := by
  have cov2 : ∀ t, t = c ∨ t = x ∨ t = y := fun t => by
    rcases h.cover t with e | e | e <;> tauto
  obtain ⟨u1, u2, u3⟩ := ord3_val h.ab h.ac h.bc
  obtain ⟨v1, v2, v3⟩ := ord3_val h.ac.symm h.bc.symm h.ab
  obtain ⟨r, hr⟩ := hN (ord3 x y c) (ord3 c x y) (ord3_inj h.ab h.ac h.bc h.cover)
    (ord3_inj h.ac.symm h.bc.symm h.ab cov2)
  obtain ⟨s0, hs0⟩ := h.col
  have htop : ∀ s', g r s' ≠ c → ord3 c x y (g r s') < ord3 c x y c := by
    intro s' hne
    rcases ord3_cases h.ac.symm h.bc.symm h.ab cov2 (g r s') with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
    · exact absurd e hne
    · omega
    · omega
  refine ⟨r, fun s hs r' => ?_⟩
  have hb := hr s ((br2_iff_of_top ⟨s0, hs0 r⟩ htop s).mpr hs) r'
  change ord3 x y c (g r' s) ≤ ord3 x y c (g r s) at hb
  rw [hs] at hb
  rcases ord3_cases h.ab h.ac h.bc h.cover (g r' s) with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
  · omega
  · omega
  · exact e

/-- Under P = (x, c, y) and Q = (y, c, x), a strict Nash row satisfies (A_x). -/
lemma condA_nec {g : A → B → X} {x y c : X} (h : Veto3 g x y c)
    (hN : ∀ u v : X → ℕ, Injective u → Injective v → ∃ r, StrictNash1 g u v r) :
    CondA g c x := by
  have covu : ∀ t, t = x ∨ t = c ∨ t = y := fun t => by
    rcases h.cover t with e | e | e <;> tauto
  have covv : ∀ t, t = y ∨ t = c ∨ t = x := fun t => by
    rcases h.cover t with e | e | e <;> tauto
  obtain ⟨u1, u2, u3⟩ := ord3_val h.ac h.ab h.bc.symm
  obtain ⟨v1, v2, v3⟩ := ord3_val h.bc h.ab.symm h.ac.symm
  obtain ⟨r, hr⟩ := hN (ord3 x c y) (ord3 y c x) (ord3_inj h.ac h.ab h.bc.symm covu)
    (ord3_inj h.bc h.ab.symm h.ac.symm covv)
  obtain ⟨r0, hr0⟩ := h.row
  obtain ⟨s0, hs0⟩ := h.col
  -- the row holds no y
  have hy : ∀ s, g r s ≠ y := by
    intro s hs
    have htop : ∀ s', g r s' ≠ y → ord3 y c x (g r s') < ord3 y c x y := by
      intro s' hne
      rcases ord3_cases h.bc h.ab.symm h.ac.symm covv (g r s') with
        ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
      · exact absurd e hne
      · omega
      · omega
    have hb := hr s ((br2_iff_of_top ⟨s, hs⟩ htop s).mpr hs) r0
    change ord3 x c y (g r0 s) ≤ ord3 x c y (g r s) at hb
    rw [hs, hr0 s] at hb
    omega
  have hxc : ∀ s, g r s = x ∨ g r s = c := fun s => by
    rcases h.cover (g r s) with e | e | e
    · exact Or.inl e
    · exact absurd e (hy s)
    · exact Or.inr e
  refine ⟨r, hxc, fun s hs r' hx => ?_⟩
  have htop : ∀ s', g r s' ≠ c → ord3 y c x (g r s') < ord3 y c x c := by
    intro s' hne
    rcases hxc s' with e | e
    · rw [e]; omega
    · exact absurd e hne
  have hb := hr s ((br2_iff_of_top ⟨s0, hs0 r⟩ htop s).mpr hs) r'
  change ord3 x c y (g r' s) ≤ ord3 x c y (g r s) at hb
  rw [hx, hs] at hb
  omega

/-- Under P = (x, y, c) and Q = (y, c, x), a strict Nash row satisfies (E_xy). -/
lemma condE_nec {g : A → B → X} {x y c : X} (h : Veto3 g x y c)
    (hN : ∀ u v : X → ℕ, Injective u → Injective v → ∃ r, StrictNash1 g u v r) :
    CondE g c x y := by
  have covv : ∀ t, t = y ∨ t = c ∨ t = x := fun t => by
    rcases h.cover t with e | e | e <;> tauto
  obtain ⟨u1, u2, u3⟩ := ord3_val h.ab h.ac h.bc
  obtain ⟨v1, v2, v3⟩ := ord3_val h.bc h.ab.symm h.ac.symm
  obtain ⟨r, hr⟩ := hN (ord3 x y c) (ord3 y c x) (ord3_inj h.ab h.ac h.bc h.cover)
    (ord3_inj h.bc h.ab.symm h.ac.symm covv)
  obtain ⟨s0, hs0⟩ := h.col
  by_cases hry : ∃ s, g r s = y
  · left
    have htop : ∀ s', g r s' ≠ y → ord3 y c x (g r s') < ord3 y c x y := by
      intro s' hne
      rcases ord3_cases h.bc h.ab.symm h.ac.symm covv (g r s') with
        ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
      · exact absurd e hne
      · omega
      · omega
    refine ⟨r, hry, fun s hs r' hx => ?_⟩
    have hb := hr s ((br2_iff_of_top hry htop s).mpr hs) r'
    change ord3 x y c (g r' s) ≤ ord3 x y c (g r s) at hb
    rw [hx, hs] at hb
    omega
  · right
    push Not at hry
    have htop : ∀ s', g r s' ≠ c → ord3 y c x (g r s') < ord3 y c x c := by
      intro s' hne
      rcases h.cover (g r s') with e | e | e
      · rw [e]; omega
      · exact absurd e (hry s')
      · exact absurd e hne
    refine ⟨r, fun s hs r' => ?_, hry⟩
    have hb := hr s ((br2_iff_of_top ⟨s0, hs0 r⟩ htop s).mpr hs) r'
    change ord3 x y c (g r' s) ≤ ord3 x y c (g r s) at hb
    rw [hs] at hb
    rcases ord3_cases h.ab h.ac h.bc h.cover (g r' s) with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
    · omega
    · omega
    · exact e

/-- **Theorem B, necessity.** -/
theorem criterion_nec {g : A → B → X} {a b c : X} (h : Veto3 g a b c)
    (hN : ¬ RationalDiagonal1 g) : Criterion g a b c := by
  rw [not_rd1_iff] at hN
  exact ⟨wall_nec h hN, condA_nec h hN, condA_nec h.swap hN, condE_nec h hN,
    condE_nec h.swap hN⟩

/-- **Theorem B.** On a form with three outcomes and a common veto c, player 1
    has no rational diagonal exactly when there is a wall row and (A_a),
    (A_b), (E_ab), (E_ba) hold. -/
theorem thmB {g : A → B → X} {a b c : X} (h : Veto3 g a b c) :
    ¬ RationalDiagonal1 g ↔ Criterion g a b c :=
  ⟨criterion_nec h, criterion_suff h⟩

/-! ### Theorem A: no common veto -/

/-- The configuration (1, (t, m, w), reverse): player 1 ranks t, m, w, player 2
    the reverse. It works when player 2 does not force w, player 1 does not
    force t, and every row inside {t, m} holding m reaches t from m. -/
lemma works_rev {g : A → B → X} {t m w : X} (htm : t ≠ m) (htw : t ≠ w) (hmw : m ≠ w)
    (hcov : ∀ x, x = t ∨ x = m ∨ x = w) (h2w : ¬ ∃ s, ∀ r, g r s = w)
    (h1t : ¬ ∃ r, ∀ s, g r s = t)
    (hC : ∀ r, (∀ s, g r s = t ∨ g r s = m) → (∃ s, g r s = m) →
      ∃ s, g r s = m ∧ ∃ r', g r' s = t) :
    RationalDiagonal1 g := by
  have covv : ∀ x, x = w ∨ x = m ∨ x = t := fun x => by
    rcases hcov x with e | e | e <;> tauto
  obtain ⟨u1, u2, u3⟩ := ord3_val htm htw hmw
  obtain ⟨v1, v2, v3⟩ := ord3_val hmw.symm htw.symm htm.symm
  refine ⟨ord3 t m w, ord3 w m t, ord3_inj htm htw hmw hcov,
    ord3_inj hmw.symm htw.symm htm.symm covv, fun r => ?_⟩
  by_cases hw : ∃ s, g r s = w
  · -- player 2's favourite in the row is w, and no column is constant w
    obtain ⟨s, hs⟩ := hw
    have htop : ∀ s', g r s' ≠ w → ord3 w m t (g r s') < ord3 w m t w := by
      intro s' hne
      rcases ord3_cases hmw.symm htw.symm htm.symm covv (g r s') with
        ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
      · exact absurd e hne
      · omega
      · omega
    refine ⟨s, (br2_iff_of_top ⟨s, hs⟩ htop s).mpr hs, fun hb => ?_⟩
    push Not at h2w
    obtain ⟨r', hr'⟩ := h2w s
    have h1 := hb r'
    change ord3 t m w (g r' s) ≤ ord3 t m w (g r s) at h1
    rw [hs] at h1
    rcases ord3_cases htm htw hmw hcov (g r' s) with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩
    · omega
    · omega
    · exact hr' e
  · push Not at hw
    have hin : ∀ s, g r s = t ∨ g r s = m := fun s => by
      rcases hcov (g r s) with e | e | e
      · exact Or.inl e
      · exact Or.inr e
      · exact absurd e (hw s)
    by_cases hm : ∃ s, g r s = m
    · -- the favourite is m, and some m-cell lies in a column holding t
      obtain ⟨s, hs, r', hr'⟩ := hC r hin hm
      have htop : ∀ s', g r s' ≠ m → ord3 w m t (g r s') < ord3 w m t m := by
        intro s' hne
        rcases hin s' with e | e
        · rw [e]; omega
        · exact absurd e hne
      refine ⟨s, (br2_iff_of_top ⟨s, hs⟩ htop s).mpr hs, fun hb => ?_⟩
      have h1 := hb r'
      change ord3 t m w (g r' s) ≤ ord3 t m w (g r s) at h1
      rw [hs, hr'] at h1
      omega
    · -- otherwise the row is constant t
      push Not at hm
      exact absurd ⟨r, fun s => (hin s).resolve_right (hm s)⟩ h1t

/-- The configuration (2, (u, t, v), rotation), with player 1's order (t, v, u).
    It works when player 2 does not force u, every column holding t reaches u
    from t, and every column inside {u, v} holding v leaves v. -/
lemma works_rot {g : A → B → X} {t u v : X} (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hcov : ∀ x, x = t ∨ x = u ∨ x = v) (h2u : ¬ ∃ s, ∀ r, g r s = u)
    (hS1 : ∀ s, (∃ r, g r s = t) → ∃ r, g r s = t ∧ ∃ s', g r s' = u)
    (hS2 : ∀ s, (∀ r, g r s = u ∨ g r s = v) → (∃ r, g r s = v) →
      ∃ r, g r s = v ∧ ∃ s', g r s' ≠ v) :
    RationalDiagonal2 g := by
  have cov1 : ∀ x, x = t ∨ x = v ∨ x = u := fun x => by
    rcases hcov x with e | e | e <;> tauto
  have cov2 : ∀ x, x = u ∨ x = t ∨ x = v := fun x => by
    rcases hcov x with e | e | e <;> tauto
  obtain ⟨u1, u2, u3⟩ := ord3_val htv htu huv.symm
  obtain ⟨v1, v2, v3⟩ := ord3_val htu.symm huv htv
  refine ⟨ord3 t v u, ord3 u t v, ord3_inj htv htu huv.symm cov1,
    ord3_inj htu.symm huv htv cov2, fun s => ?_⟩
  by_cases ht : ∃ r, g r s = t
  · -- player 1's favourite in the column is t; its row holds u
    obtain ⟨r, hr, s', hs'⟩ := hS1 s ht
    refine ⟨r, fun r' => ?_, fun hb => ?_⟩
    · show ord3 t v u (g r' s) ≤ ord3 t v u (g r s)
      rw [hr]
      rcases ord3_cases htv htu huv.symm cov1 (g r' s) with ⟨e, hv⟩ | ⟨e, hv⟩ | ⟨e, hv⟩ <;>
        omega
    · have h1 := hb s'
      change ord3 u t v (g r s') ≤ ord3 u t v (g r s) at h1
      rw [hr, hs'] at h1
      omega
  · push Not at ht
    have hin : ∀ r, g r s = u ∨ g r s = v := fun r => by
      rcases hcov (g r s) with e | e | e
      · exact absurd e (ht r)
      · exact Or.inl e
      · exact Or.inr e
    by_cases hv : ∃ r, g r s = v
    · -- the favourite is v; some v-cell lies in a row holding another outcome
      obtain ⟨r, hr, s', hs'⟩ := hS2 s hin hv
      refine ⟨r, fun r' => ?_, fun hb => ?_⟩
      · show ord3 t v u (g r' s) ≤ ord3 t v u (g r s)
        rw [hr]
        rcases hin r' with e | e
        · rw [e]; omega
        · rw [e]
      · have h1 := hb s'
        change ord3 u t v (g r s') ≤ ord3 u t v (g r s) at h1
        rw [hr] at h1
        rcases ord3_cases htu.symm huv htv cov2 (g r s') with ⟨e, hv'⟩ | ⟨e, hv'⟩ | ⟨e, hv'⟩
        · omega
        · omega
        · exact hs' e
    · -- otherwise the column is constant u
      push Not at hv
      exact absurd ⟨s, fun r => (hin r).resolve_right (hv r)⟩ h2u

/-- The core of Theorem A: if player 2 forces no single outcome and player 1
    does not force an outcome t that occurs, then some player has a rational
    diagonal. One of the three configurations (1, (t, u, v), reverse),
    (1, (t, v, u), reverse) and (2, (u, t, v), rotation) works. -/
lemma thmA_core {g : A → B → X} {t u v : X} (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hcov : ∀ x, x = t ∨ x = u ∨ x = v) (ht : ∃ r s, g r s = t)
    (h2 : ∀ x, ¬ ∃ s, ∀ r, g r s = x) (h1t : ¬ ∃ r, ∀ s, g r s = t) :
    RationalDiagonal1 g ∨ RationalDiagonal2 g := by
  have cov' : ∀ x, x = t ∨ x = v ∨ x = u := fun x => by
    rcases hcov x with e | e | e <;> tauto
  by_cases hCu : ∀ r, (∀ s, g r s = t ∨ g r s = u) → (∃ s, g r s = u) →
      ∃ s, g r s = u ∧ ∃ r', g r' s = t
  · exact Or.inl (works_rev htu htv huv hcov (h2 v) h1t hCu)
  by_cases hCv : ∀ r, (∀ s, g r s = t ∨ g r s = v) → (∃ s, g r s = v) →
      ∃ s, g r s = v ∧ ∃ r', g r' s = t
  · exact Or.inl (works_rev htv htu huv.symm cov' (h2 u) h1t hCv)
  push Not at hCu hCv
  obtain ⟨ru, hu_in, ⟨su, hsu⟩, hu_out⟩ := hCu
  obtain ⟨rv, hv_in, -, hv_out⟩ := hCv
  refine Or.inr (works_rot htu htv huv hcov (h2 u) (fun s hst => ?_) (fun s hin _ => ?_))
  · -- Step 1: every column holding t reaches u from t
    obtain ⟨r1, hr1⟩ := hst
    by_contra hno
    push Not at hno
    rcases hu_in s with e | e
    · exact hno ru e su hsu
    · exact hu_out s e r1 hr1
  · -- Step 2: every column inside {u, v} holding v leaves v
    by_contra hno
    push Not at hno
    have hcell : g rv s = v := by
      rcases hv_in s with e | e
      · rcases hin rv with e' | e'
        · exact absurd (e.symm.trans e') htu
        · exact absurd (e.symm.trans e') htv
      · exact e
    have hall := hno rv hcell
    obtain ⟨r1, s1, hs1⟩ := ht
    exact hv_out s1 (hall s1) r1 hs1

/-- **Theorem A.** Let a form with three outcomes, all occurring, be
    non-dictatorial, with no outcome forced by both players. Then some player
    has a rational diagonal. -/
theorem thmA {g : A → B → X} {a b c : X} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hcov : ∀ x, x = a ∨ x = b ∨ x = c) (honto : ∀ x, ∃ r s, g r s = x)
    (hveto : ¬ ∃ x, (∃ r, ∀ s, g r s = x) ∧ ∃ s, ∀ r, g r s = x)
    (hnd1 : ¬ ∀ x, ∃ r, ∀ s, g r s = x) (hnd2 : ¬ ∀ x, ∃ s, ∀ r, g r s = x) :
    RationalDiagonal1 g ∨ RationalDiagonal2 g := by
  -- the two other outcomes, for any outcome t
  have others : ∀ t : X, ∃ u v : X, t ≠ u ∧ t ≠ v ∧ u ≠ v ∧ ∀ x, x = t ∨ x = u ∨ x = v := by
    intro t
    rcases hcov t with rfl | rfl | rfl
    · exact ⟨b, c, hab, hac, hbc, hcov⟩
    · exact ⟨a, c, hab.symm, hbc, hac, fun x => by rcases hcov x with e | e | e <;> tauto⟩
    · exact ⟨a, b, hac.symm, hbc.symm, hab, fun x => by rcases hcov x with e | e | e <;> tauto⟩
  by_cases h2 : ∀ x, ¬ ∃ s, ∀ r, g r s = x
  · -- player 2 forces nothing; player 1 is not a dictator
    push Not at hnd1
    obtain ⟨t, ht⟩ := hnd1
    obtain ⟨u, v, htu, htv, huv, hc⟩ := others t
    exact thmA_core htu htv huv hc (honto t) h2 (by push Not; exact ht)
  · -- player 2 forces some x, so player 1 forces nothing: exchange the players
    push Not at h2
    obtain ⟨x, s, hs⟩ := h2
    have h1 : ∀ y, ¬ ∃ r, ∀ s, g r s = y := by
      rintro y ⟨r, hr⟩
      have hxy : x = y := (hs r).symm.trans (hr s)
      subst hxy
      exact hveto ⟨x, ⟨r, hr⟩, ⟨s, hs⟩⟩
    push Not at hnd2
    obtain ⟨t, ht⟩ := hnd2
    obtain ⟨u, v, htu, htv, huv, hc⟩ := others t
    obtain ⟨r0, s0, h0⟩ := honto t
    rcases thmA_core (g := transpose g) htu htv huv hc ⟨s0, r0, h0⟩ h1
      (by push Not; exact ht) with h | h
    · exact Or.inr ((rd2_iff g).mpr h)
    · exact Or.inl ((rd2_iff (transpose g)).mp h)

/-! ### Proposition 5‴ -/

/-- Without a rational diagonal for either player, there is a common veto. -/
theorem veto_of_no_diagonal {g : A → B → X} {a b c : X} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) (hcov : ∀ x, x = a ∨ x = b ∨ x = c) (honto : ∀ x, ∃ r s, g r s = x)
    (hnd1 : ¬ ∀ x, ∃ r, ∀ s, g r s = x) (hnd2 : ¬ ∀ x, ∃ s, ∀ r, g r s = x)
    (h1 : ¬ RationalDiagonal1 g) (h2 : ¬ RationalDiagonal2 g) :
    ∃ x, (∃ r, ∀ s, g r s = x) ∧ ∃ s, ∀ r, g r s = x := by
  by_contra hv
  rcases thmA hab hac hbc hcov honto hv hnd1 hnd2 with h | h
  · exact h1 h
  · exact h2 h

omit [DecidableEq X] in
/-- The setting of Theorem B is symmetric in the players. -/
theorem Veto3.transpose {g : A → B → X} {a b c : X} (h : Veto3 g a b c) :
    Veto3 (TwoPlayer.transpose g) a b c := by
  obtain ⟨r1, s1, e1⟩ := h.onto_a
  obtain ⟨r2, s2, e2⟩ := h.onto_b
  exact ⟨h.ab, h.ac, h.bc, h.cover, h.col, h.row, ⟨s1, r1, e1⟩, ⟨s2, r2, e2⟩⟩

/-- **Proposition 5‴, with a common veto c.** Neither player has a rational
    diagonal exactly when both satisfy the criterion of Theorem B, player 2's
    read on columns. -/
theorem prop5 {g : A → B → X} {a b c : X} (h : Veto3 g a b c) :
    (¬ RationalDiagonal1 g ∧ ¬ RationalDiagonal2 g) ↔
      Criterion g a b c ∧ Criterion (TwoPlayer.transpose g) a b c := by
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(thmB h).mp h1, (thmB h.transpose).mp fun hr => h2 ((rd2_iff g).mpr hr)⟩
  · rintro ⟨c1, c2⟩
    exact ⟨(thmB h).mpr c1, fun hr => (thmB h.transpose).mpr c2 ((rd2_iff g).mp hr)⟩

end Necessity

end ThreeOutcomes
