/-
  Gibbard (1973), "Manipulation of voting schemes: a general result",
  Econometrica 41, 587–601. Main theorem:

    Every straightforward game form with at least three possible outcomes
    is dictatorial.

  The proof follows Gibbard's Section 3 step by step: the operator P * Z,
  the social welfare function f, Assertion 1 and its three corollaries,
  Assertion 2 (f gives orderings), Assertion 3 (Arrow's theorem gives a
  dictator for f) and Assertion 4 (the dictator for f is a dictator for g).
  Uses only core Lean and `Arrow.lean`.

  Encoding. All players draw strategies from one type St. A game form with
  different strategy sets S₁, …, Sₙ is covered by taking St to be their union
  and letting a player's strategies outside its own set act like a fixed
  strategy of its own set; this changes neither straightforwardness nor
  dictatorship. The outcome set X is the range of g (field `onto`), as in
  Gibbard's definition. Outcomes and players are finite (lists `allX`,
  `allI`); strategy sets need not be.
-/

module

public import Arrow

@[expose] public section

namespace Gibbard73

open Arrow

variable {X I St : Type} [DecidableEq X] [DecidableEq I]

/-! ### Game forms -/

/-- s with the k-th strategy replaced by t (Gibbard's s_k/t). -/
def upd (s : I → St) (k : I) (t : St) : I → St := fun i => if i = k then t else s i

omit [DecidableEq X] in
theorem upd_upd (s : I → St) (k : I) (a b : St) : upd (upd s k a) k b = upd s k b := by
  funext i
  by_cases h : i = k <;> simp [upd, h]

omit [DecidableEq X] in
theorem upd_self (s : I → St) (k : I) : upd s k (s k) = s := by
  funext i
  by_cases h : i = k
  · rw [h]
    simp [upd]
  · simp [upd, h]

/-- t is P-dominant for k: for every s, g(s_k/t) R g(s), i.e. not g(s) P g(s_k/t). -/
def Dominant (g : (I → St) → X) (P : Rel X) (k : I) (t : St) : Prop :=
  ∀ s : I → St, P (g s) (g (upd s k t)) = false

/-- For every preference ordering and player there is a dominant strategy. -/
def Straightforward (g : (I → St) → X) : Prop :=
  ∀ P : Rel X, IsOrdering P → ∀ k : I, ∃ t : St, Dominant g P k t

/-- k can force every outcome. -/
def IsDictator (g : (I → St) → X) (k : I) : Prop :=
  ∀ x : X, ∃ t : St, ∀ s : I → St, s k = t → g s = x

/-- A game form with finitely many outcomes, all of them reached, finitely
    many players, and at least three distinct outcomes. -/
structure GameForm (X I St : Type) where
  allX : List X
  hallX : ∀ x, x ∈ allX
  allI : List I
  hallI : ∀ i, i ∈ allI
  g : (I → St) → X
  onto : ∀ x, ∃ s, g s = x
  a : X
  b : X
  c : X
  hab : a ≠ b
  hac : a ≠ c
  hbc : b ≠ c

omit [DecidableEq X] [DecidableEq I] in
/-- With at least two outcomes there is at least one player. -/
theorem exists_player (Gf : GameForm X I St) : ∃ _ : I, True := by
  cases h : Gf.allI with
  | cons i _ => exact ⟨i, trivial⟩
  | nil =>
    exfalso
    obtain ⟨s, hs⟩ := Gf.onto Gf.a
    obtain ⟨s', hs'⟩ := Gf.onto Gf.b
    have e : s = s' := funext fun i => by
      have := Gf.hallI i
      rw [h] at this
      cases this
    apply Gf.hab
    rw [← hs, ← hs', e]

/-! ### The fixed chain ordering Q: position in the list of outcomes -/

/-- Position of the first occurrence of x. -/
def idx : List X → X → Nat
  | [], _ => 0
  | a :: l, x => if a = x then 0 else idx l x + 1

theorem idx_inj : ∀ (l : List X) (x y : X), x ∈ l → y ∈ l → idx l x = idx l y → x = y
  | [], _, _, hx, _, _ => by cases hx
  | a :: l, x, y, hx, hy, h => by
    by_cases hax : a = x
    · subst hax
      by_cases hay : a = y
      · exact hay
      · simp [idx, hay] at h
    · by_cases hay : a = y
      · subst hay
        simp [idx, hax] at h
      · simp [idx, hax, hay] at h
        have hx' : x ∈ l := by
          rcases List.mem_cons.mp hx with e | e
          · exact absurd e.symm hax
          · exact e
        have hy' : y ∈ l := by
          rcases List.mem_cons.mp hy with e | e
          · exact absurd e.symm hay
          · exact e
        exact idx_inj l x y hx' hy' h

/-! ### Lexicographic orderings and the operator P * Z -/

abbrev lt3 (a b c a' b' c' : Nat) : Prop := a < a' ∨ (a = a' ∧ (b < b' ∨ (b = b' ∧ c < c')))

/-- Compare three keys lexicographically. -/
def lexRel (k₁ k₂ k₃ : X → Nat) : Rel X :=
  fun x y => decide (lt3 (k₁ x) (k₂ x) (k₃ x) (k₁ y) (k₂ y) (k₃ y))

omit [DecidableEq X] in
theorem lexRel_ord (k₁ k₂ k₃ : X → Nat) : IsOrdering (lexRel k₁ k₂ k₃) where
  asymm := by
    intro x y h
    simp only [lexRel, lt3, decide_eq_true_eq] at h
    simp only [lexRel, lt3, decide_eq_false_iff_not]
    omega
  negTrans := by
    intro x y z h
    simp only [lexRel, lt3, decide_eq_true_eq] at h ⊢
    omega

/-- Number of members of Z strictly above x. -/
def zRank (allX : List X) (P : Rel X) (Z : X → Bool) (x : X) : Nat :=
  countIf (fun t => Z t && P t x) allX

omit [DecidableEq X] in
theorem zRank_spec (allX : List X) (hallX : ∀ x, x ∈ allX) (P : Rel X) (hP : IsOrdering P)
    (Z : X → Bool) (x y : X) (hx : Z x = true) :
    P x y = true ↔ zRank allX P Z x < zRank allX P Z y := by
  constructor
  · intro h
    exact countIf_strict (fun t => Z t && P t x) (fun t => Z t && P t y)
      (fun t ht => by
        simp only [Bool.and_eq_true] at ht ⊢
        exact ⟨ht.1, ord_trans hP ht.2 h⟩)
      x (by simp [hx, h]) (by simp [ord_irrefl hP x]) allX (hallX x)
  · intro hlt
    cases hxy : P x y with
    | true => rfl
    | false =>
      have hle : zRank allX P Z y ≤ zRank allX P Z x :=
        countIf_mono (fun t => Z t && P t y) (fun t => Z t && P t x) (fun t ht => by
          simp only [Bool.and_eq_true] at ht ⊢
          refine ⟨ht.1, ?_⟩
          rcases hP.negTrans t x y ht.2 with h | h
          · exact h
          · rw [hxy] at h
            cases h) allX
      omega

/-- Gibbard's P * Z: members of Z on top, ordered by P with ties broken by Q;
    everything else below, ordered by Q. -/
def star (allX : List X) (P : Rel X) (Z : X → Bool) : Rel X :=
  lexRel (fun t => if Z t = true then 0 else 1)
    (fun t => if Z t = true then zRank allX P Z t else 0) (idx allX)

theorem star_ord (allX : List X) (P : Rel X) (Z : X → Bool) : IsOrdering (star allX P Z) :=
  lexRel_ord _ _ _

/-- (i) P * Z is a chain ordering. -/
theorem star_chain (allX : List X) (hallX : ∀ x, x ∈ allX) (P : Rel X) (Z : X → Bool)
    (x y : X) (hxy : x ≠ y) : star allX P Z x y = true ∨ star allX P Z y x = true := by
  have hi : idx allX x ≠ idx allX y := fun e => hxy (idx_inj allX x y (hallX x) (hallX y) e)
  simp only [star, lexRel, lt3, decide_eq_true_eq]
  omega

/-- (3a), in Bool form: on Z, x (P * Z) y iff x P y, or neither is preferred
    and x comes first in Q. -/
theorem star_in_in (allX : List X) (hallX : ∀ x, x ∈ allX) (P : Rel X) (hP : IsOrdering P)
    (Z : X → Bool) (x y : X) (hx : Z x = true) (hy : Z y = true) :
    star allX P Z x y = (P x y || (!P y x && decide (idx allX x < idx allX y))) := by
  have s₁ := zRank_spec allX hallX P hP Z x y hx
  have s₂ := zRank_spec allX hallX P hP Z y x hy
  cases h₁ : P x y <;> cases h₂ : P y x
  · simp [h₁] at s₁
    simp [h₂] at s₂
    have e : zRank allX P Z x = zRank allX P Z y := by omega
    simp [star, lexRel, lt3, hx, hy, e]
  · simp [h₁] at s₁
    simp [h₂] at s₂
    simp [star, lexRel, lt3, hx, hy]
    omega
  · simp [h₁] at s₁
    simp [h₂] at s₂
    simp [star, lexRel, lt3, hx, hy]
    omega
  · have := hP.asymm x y h₁
    rw [h₂] at this
    cases this

/-- (3b) Members of Z are above non-members. -/
theorem star_in_out (allX : List X) (P : Rel X) (Z : X → Bool) (x y : X)
    (hx : Z x = true) (hy : Z y = false) : star allX P Z x y = true := by
  simp [star, lexRel, lt3, hx, hy]

theorem star_out_in (allX : List X) (P : Rel X) (Z : X → Bool) (x y : X)
    (hx : Z x = false) (hy : Z y = true) : star allX P Z x y = false := by
  simp [star, lexRel, lt3, hx, hy]

/-- (3c) Non-members are ordered by Q. -/
theorem star_out_out (allX : List X) (P : Rel X) (Z : X → Bool) (x y : X)
    (hx : Z x = false) (hy : Z y = false) :
    star allX P Z x y = decide (idx allX x < idx allX y) := by
  simp [star, lexRel, lt3, hx, hy]

omit [DecidableEq X] in
theorem countIf_congr {V : Type} (A B : V → Bool) (h : ∀ t, A t = B t) (l : List V) :
    countIf A l = countIf B l :=
  Nat.le_antisymm
    (countIf_mono A B (fun t ht => by rw [← h t]; exact ht) l)
    (countIf_mono B A (fun t ht => by rw [h t]; exact ht) l)

/-- (iii) If P and P' agree on Z, then P * Z = P' * Z. -/
theorem star_agree (allX : List X) (P P' : Rel X) (Z : X → Bool)
    (hag : ∀ u t, Z u = true → Z t = true → P u t = P' u t) :
    star allX P Z = star allX P' Z := by
  have hz : ∀ t, Z t = true → zRank allX P Z t = zRank allX P' Z t := by
    intro t ht
    apply countIf_congr
    intro u
    cases hu : Z u with
    | false => rfl
    | true => simp [hag u t hu ht]
  have hk : (fun t => if Z t = true then zRank allX P Z t else 0) =
      (fun t => if Z t = true then zRank allX P' Z t else 0) := by
    funext t
    cases ht : Z t with
    | false => rfl
    | true => simp [hz t ht]
  unfold star
  rw [hk]

/-- (ii) If Y ⊆ Z, then (P * Z) * Y = P * Y. -/
theorem star_sub (allX : List X) (hallX : ∀ x, x ∈ allX) (P : Rel X) (hP : IsOrdering P)
    (Z Y : X → Bool) (hYZ : ∀ t, Y t = true → Z t = true) :
    star allX (star allX P Z) Y = star allX P Y := by
  funext x y
  cases hx : Y x <;> cases hy : Y y
  · rw [star_out_out allX _ Y x y hx hy, star_out_out allX _ Y x y hx hy]
  · rw [star_out_in allX _ Y x y hx hy, star_out_in allX _ Y x y hx hy]
  · rw [star_in_out allX _ Y x y hx hy, star_in_out allX _ Y x y hx hy]
  · rw [star_in_in allX hallX (star allX P Z) (star_ord allX P Z) Y x y hx hy,
      star_in_in allX hallX P hP Z x y (hYZ x hx) (hYZ y hy),
      star_in_in allX hallX P hP Z y x (hYZ y hy) (hYZ x hx),
      star_in_in allX hallX P hP Y x y hx hy]
    cases P x y <;> cases P y x <;> cases decide (idx allX x < idx allX y) <;>
      cases decide (idx allX y < idx allX x) <;> rfl

/-! ### Pairs and triples -/

def pairZ (x y : X) : X → Bool := fun t => decide (t = x) || decide (t = y)
def tripleZ (x y z : X) : X → Bool := fun t => decide (t = x) || decide (t = y) || decide (t = z)

theorem pairZ_comm (x y : X) : pairZ x y = pairZ y x := by
  funext t
  simp [pairZ, Bool.or_comm]

theorem pairZ_left (x y : X) : pairZ x y x = true := by simp [pairZ]
theorem pairZ_right (x y : X) : pairZ x y y = true := by simp [pairZ]
theorem pairZ_other (x y t : X) (h₁ : t ≠ x) (h₂ : t ≠ y) : pairZ x y t = false := by
  simp [pairZ, h₁, h₂]

/-! ### Fixing dominant strategies: the voting scheme v and the welfare function f -/

/-- For every player and ordering a dominant strategy (Gibbard's σᵢ). -/
structure Strat (Gf : GameForm X I St) where
  σ : I → Rel X → St
  dom : ∀ k P, IsOrdering P → Dominant Gf.g P k (σ k P)

variable (Gf : GameForm X I St) (S : Strat Gf)

/-- v(P) = g(σ(P)). -/
def v (P : I → Rel X) : X := Gf.g (fun i => S.σ i (P i))

/-- The profile P * Z. -/
def starP (P : I → Rel X) (Z : X → Bool) : I → Rel X := fun i => star Gf.allX (P i) Z

/-- x f(P) y iff x ≠ y and x = v(P * {x, y}). -/
def fP (P : I → Rel X) : Rel X :=
  fun x y => decide (x ≠ y) && decide (x = v Gf S (starP Gf P (pairZ x y)))

/-! ### Assertion 1 -/

/-- Assertion 1. Let s = σ(P) and x ≠ y. Suppose (4a) everyone who prefers
    y to x plays as in s, (4b) nobody is indifferent between x and y, and
    (4c) y R x. Then g(s') ≠ x.
    Gibbard's hypothesis x ≠ y is kept for fidelity but not needed: (4b)
    already excludes x = y, since nobody strictly prefers x to itself. -/
theorem assertion1 (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) (s' : I → St) (x y : X)
    (_hxy : x ≠ y)
    (h4a : ∀ i, P i y x = true → s' i = S.σ i (P i))
    (h4b : ∀ i, P i x y = true ∨ P i y x = true)
    (h4c : v Gf S (starP Gf P (pairZ x y)) ≠ x) : Gf.g s' ≠ x := by
  intro hgx
  let Ps := starP Gf P (pairZ x y)
  let t : I → St := fun i => S.σ i (Ps i)
  have hgt : Gf.g t ≠ x := h4c
  -- the sequence s⁰ = s', …, sⁿ = t, replacing one player at a time
  let hyb : List I → I → St := fun L i => if i ∈ L then t i else s' i
  have step : ∀ L : List I, Gf.g (hyb L) ≠ x →
      ∃ k M, Gf.g (hyb M) = x ∧ Gf.g (upd (hyb M) k (t k)) ≠ x := by
    intro L
    induction L with
    | nil =>
      intro h
      exfalso
      apply h
      have e : hyb [] = s' := by
        funext i
        simp [hyb]
      rw [e]
      exact hgx
    | cons k M ih =>
      intro h
      by_cases hM : Gf.g (hyb M) = x
      · refine ⟨k, M, hM, ?_⟩
        have e : upd (hyb M) k (t k) = hyb (k :: M) := by
          funext i
          by_cases hik : i = k
          · rw [hik]
            simp [upd, hyb]
          · simp [upd, hyb, hik]
        rw [e]
        exact h
      · exact ih hM
  have hall : hyb Gf.allI = t := by
    funext i
    simp [hyb, Gf.hallI i]
  obtain ⟨k, M, hM, hk⟩ := step Gf.allI (by rw [hall]; exact hgt)
  let u := upd (hyb M) k (t k)
  have hu : Gf.g u ≠ x := hk
  -- player k was still playing s'_k at step k − 1
  have hMk : hyb M k = s' k := by
    by_cases hkM : k ∈ M
    · exfalso
      have e : u = hyb M := by
        funext i
        by_cases hik : i = k
        · rw [hik]
          simp [u, upd, hyb, hkM]
        · simp [u, upd, hik]
      apply hu
      rw [e]
      exact hM
    · simp [hyb, hkM]
  have hback : upd u k (s' k) = hyb M := by
    show upd (upd (hyb M) k (t k)) k (s' k) = hyb M
    rw [upd_upd, ← hMk, upd_self]
  by_cases hc : Gf.g u = y ∧ P k y x = true
  · -- Case 1: s'_k = σ_k(P_k) is not P_k-dominant
    have hs'k : s' k = S.σ k (P k) := h4a k hc.2
    have hd := S.dom k (P k) (hP k) u
    rw [← hs'k, hback, hM, hc.1, hc.2] at hd
    cases hd
  · -- Case 2: t_k = σ_k(P*_k) is not P*_k-dominant
    have hx' : star Gf.allX (P k) (pairZ x y) x (Gf.g u) = true := by
      by_cases hgy : Gf.g u = y
      · have hxyk : P k x y = true := by
          rcases h4b k with h | h
          · exact h
          · exact absurd ⟨hgy, h⟩ hc
        rw [hgy, star_in_in Gf.allX Gf.hallX (P k) (hP k) (pairZ x y) x y
          (pairZ_left x y) (pairZ_right x y), hxyk]
        simp
      · exact star_in_out Gf.allX (P k) (pairZ x y) x (Gf.g u) (pairZ_left x y)
          (pairZ_other x y (Gf.g u) hu hgy)
    have hd := S.dom k (Ps k) (star_ord Gf.allX (P k) (pairZ x y)) (hyb M)
    rw [hM] at hd
    have hd' : star Gf.allX (P k) (pairZ x y) x (Gf.g u) = false := hd
    rw [hx'] at hd'
    cases hd'

/-! ### Corollaries 1–3 -/

/-- Corollary 1 (unanimity). -/
theorem cor1 (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) (x y : X)
    (h : ∀ i, P i x y = true) : fP Gf S P x y = true := by
  have hxy : x ≠ y := by
    intro e
    obtain ⟨i₀, _⟩ := exists_player Gf
    have := h i₀
    rw [e, ord_irrefl (hP i₀)] at this
    cases this
  have hv : x = v Gf S (starP Gf P (pairZ x y)) := by
    apply Classical.byContradiction
    intro hne
    obtain ⟨s', hs'⟩ := Gf.onto x
    exact assertion1 Gf S P hP s' x y hxy
      (fun i hyx => by
        rw [(hP i).asymm x y (h i)] at hyx
        cases hyx)
      (fun i => Or.inl (h i)) (fun e => hne e.symm) hs'
  simp [fP, hxy, ← hv]

/-- Corollary 2. -/
theorem cor2 (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) (x y : X) (hxy : x ≠ y)
    (h4b : ∀ i, P i x y = true ∨ P i y x = true) (hf : fP Gf S P x y = false) :
    v Gf S P ≠ x := by
  have h4c : v Gf S (starP Gf P (pairZ x y)) ≠ x := by
    intro e
    unfold fP at hf
    rw [e] at hf
    simp [hxy] at hf
  exact assertion1 Gf S P hP (fun i => S.σ i (P i)) x y hxy (fun _ _ => rfl) h4b h4c

/-- Corollary 3. -/
theorem cor3 (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) (x y : X) (hxy : x ≠ y)
    (h4b : ∀ i, P i x y = true ∨ P i y x = true) (hv : v Gf S P = x) :
    fP Gf S P x y = true := by
  cases hf : fP Gf S P x y with
  | true => rfl
  | false => exact absurd hv (cor2 Gf S P hP x y hxy h4b hf)

/-! ### Assertion 2: f(P) is an ordering -/

theorem fP_asymm (P : I → Rel X) (x y : X) (h : fP Gf S P x y = true) :
    fP Gf S P y x = false := by
  have h' : x ≠ y ∧ x = v Gf S (starP Gf P (pairZ x y)) := by
    simpa [fP] using h
  show (decide (y ≠ x) && decide (y = v Gf S (starP Gf P (pairZ y x)))) = false
  rw [pairZ_comm y x, ← h'.2]
  simp [Ne.symm h'.1]

/-- f(P * {x, y, z}) and f(P) agree on pairs from {x, y, z}. -/
theorem fP_triple (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) (x y z a b : X)
    (ha : tripleZ x y z a = true) (hb : tripleZ x y z b = true) :
    fP Gf S (starP Gf P (tripleZ x y z)) a b = fP Gf S P a b := by
  have e : starP Gf (starP Gf P (tripleZ x y z)) (pairZ a b) = starP Gf P (pairZ a b) := by
    funext i
    apply star_sub Gf.allX Gf.hallX (P i) (hP i)
    intro t ht
    simp only [pairZ, Bool.or_eq_true, decide_eq_true_eq] at ht
    rcases ht with e | e <;> rw [e] <;> assumption
  unfold fP
  rw [e]

theorem assertion2 (P : I → Rel X) (hP : ∀ i, IsOrdering (P i)) :
    IsOrdering (fP Gf S P) where
  asymm := fP_asymm Gf S P
  negTrans := by
    intro x y z hxz
    let P' := starP Gf P (tripleZ x y z)
    have hP' : ∀ i, IsOrdering (P' i) := fun i => star_ord Gf.allX (P i) _
    have chain : ∀ i a b, a ≠ b → P' i a b = true ∨ P' i b a = true :=
      fun i a b h => star_chain Gf.allX Gf.hallX (P i) _ a b h
    have tx : tripleZ x y z x = true := by simp [tripleZ]
    have ty : tripleZ x y z y = true := by simp [tripleZ]
    have tz : tripleZ x y z z = true := by simp [tripleZ]
    have hxz' : fP Gf S P' x z = true := by
      rw [fP_triple Gf S P hP x y z x z tx tz]
      exact hxz
    have hxzne : x ≠ z := by
      intro e
      simp [fP, e] at hxz
    by_cases hyx : y = x
    · right
      rw [hyx]
      exact hxz
    by_cases hyz : y = z
    · left
      rw [hyz]
      exact hxz
    by_cases hv : v Gf S P' = x
    · -- Case 1
      left
      rw [← fP_triple Gf S P hP x y z x y tx ty]
      exact cor3 Gf S P' hP' x y (Ne.symm hyx) (fun i => chain i x y (Ne.symm hyx)) hv
    · -- Case 2: by elimination v(P') = y
      right
      have hz : v Gf S P' ≠ z :=
        cor2 Gf S P' hP' z x (Ne.symm hxzne) (fun i => chain i z x (Ne.symm hxzne))
          (fP_asymm Gf S P' x z hxz')
      have hw : ∀ w, w ≠ x → w ≠ y → w ≠ z → v Gf S P' ≠ w := by
        intro w h₁ h₂ h₃
        have tw : tripleZ x y z w = false := by simp [tripleZ, h₁, h₂, h₃]
        have hxw : fP Gf S P' x w = true :=
          cor1 Gf S P' hP' x w (fun i => star_in_out Gf.allX (P i) _ x w tx tw)
        exact cor2 Gf S P' hP' w x h₁ (fun i => chain i w x h₁) (fP_asymm Gf S P' x w hxw)
      have hvy : v Gf S P' = y := by
        apply Classical.byContradiction
        intro hne
        exact hw _ hv hne hz rfl
      rw [← fP_triple Gf S P hP x y z y z ty tz]
      exact cor3 Gf S P' hP' y z hyz (fun i => chain i y z hyz) hvy

/-! ### Assertion 3: f satisfies the Arrow conditions, so it has a dictator -/

theorem arrowConditions : ArrowConditions (fP Gf S) where
  ordering := assertion2 Gf S
  unanimity := cor1 Gf S
  pairwise := by
    intro P P' hP hP' x y hxy hyx
    have e : starP Gf P (pairZ x y) = starP Gf P' (pairZ x y) := by
      funext i
      apply star_agree
      intro u t hu ht
      simp only [pairZ, Bool.or_eq_true, decide_eq_true_eq] at hu ht
      rcases hu with hu | hu <;> rcases ht with ht | ht <;> rw [hu, ht]
      · rw [ord_irrefl (hP i), ord_irrefl (hP' i)]
      · exact hxy i
      · exact hyx i
      · rw [ord_irrefl (hP i), ord_irrefl (hP' i)]
    unfold fP
    rw [e]

theorem assertion3 : ∃ k : I, ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) →
    ∀ x y, P k x y = true → fP Gf S P x y = true :=
  Arrow.arrow ⟨Gf.allX, Gf.hallX, fP Gf S, arrowConditions Gf S,
    Gf.a, Gf.b, Gf.c, Gf.hab, Gf.hac, Gf.hbc⟩ Gf.allI Gf.hallI

/-! ### Assertion 4: the dictator for f is a dictator for g -/

theorem assertion4 (k : I) (hk : ∀ P : I → Rel X, (∀ i, IsOrdering (P i)) →
    ∀ x y, P k x y = true → fP Gf S P x y = true) : IsDictator Gf.g k := by
  intro y
  let Py : Rel X := relOf (fun t => if t = y then 0 else 1)
  refine ⟨S.σ k Py, ?_⟩
  intro s' hs'k
  apply Classical.byContradiction
  intro hne
  let x := Gf.g s'
  have hxy : x ≠ y := hne
  let Px : Rel X := relOf (fun t => if t = x then 0 else 1)
  let P : I → Rel X := fun i => if i = k then Py else Px
  have hPk : P k = Py := by simp [P]
  have hPi : ∀ i, i ≠ k → P i = Px := fun i e => by simp [P, e]
  have hP : ∀ i, IsOrdering (P i) := by
    intro i
    by_cases e : i = k
    · rw [e, hPk]
      exact relOf_ord _
    · rw [hPi i e]
      exact relOf_ord _
  have yx_k : Py y x = true := by simp [Py, relOf, hxy]
  have xy_o : Px x y = true := by simp [Px, relOf, Ne.symm hxy]
  have yx_o : Px y x = false := by simp [Px, relOf, Ne.symm hxy]
  -- y f(P) x, since k is dictator for f
  have hyx : fP Gf S P y x = true := hk P hP y x (by rw [hPk]; exact yx_k)
  have h4c : v Gf S (starP Gf P (pairZ x y)) ≠ x := by
    intro e
    have hxy' := fP_asymm Gf S P y x hyx
    unfold fP at hxy'
    rw [e] at hxy'
    simp [hxy] at hxy'
  have := assertion1 Gf S P hP s' x y hxy
    (fun i h => by
      by_cases e : i = k
      · rw [e, hs'k, hPk]
      · rw [hPi i e, yx_o] at h
        cases h)
    (fun i => by
      by_cases e : i = k
      · right
        rw [e, hPk]
        exact yx_k
      · left
        rw [hPi i e]
        exact xy_o)
    h4c
  exact this rfl

/-! ### Gibbard's theorem -/

omit [DecidableEq X] in
/-- From straightforwardness, choose a dominant strategy for every player
    and ordering. -/
theorem exists_strat (Gf : GameForm X I St) (hs : Straightforward Gf.g) :
    Nonempty (Strat Gf) := by
  have hex : ∀ (k : I) (P : Rel X), ∃ t : St, IsOrdering P → Dominant Gf.g P k t := by
    intro k P
    rcases Classical.em (IsOrdering P) with hP | hP
    · obtain ⟨t, ht⟩ := hs P hP k
      exact ⟨t, fun _ => ht⟩
    · obtain ⟨s₀, _⟩ := Gf.onto Gf.a
      exact ⟨s₀ k, fun h => absurd h hP⟩
  exact ⟨⟨fun k P => Classical.choose (hex k P), fun k P hP => Classical.choose_spec (hex k P) hP⟩⟩

/-- Gibbard (1973): every straightforward game form with at least three
    possible outcomes is dictatorial. -/
theorem gibbard (Gf : GameForm X I St) (hs : Straightforward Gf.g) :
    ∃ k, IsDictator Gf.g k := by
  obtain ⟨S⟩ := exists_strat Gf hs
  obtain ⟨k, hk⟩ := assertion3 Gf S
  exact ⟨k, assertion4 Gf S k hk⟩

end Gibbard73
