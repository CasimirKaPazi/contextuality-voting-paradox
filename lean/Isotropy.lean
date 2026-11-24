module

public import Mathlib

@[expose] public section

/-!
# The isotropy lemma

*Where the Symmetry Goes*, Lemma (isotropy), for any group acting on inputs and outputs.

A rule `f : X → Y` is *equivariant* (for renamings of alternatives: neutral) when
`f (g • x) = g • f x`. Admissible outputs are given by a family `A x ⊆ Y` that the group carries
along (`g • A x ⊆ A (g • x)`).

* `fixed_of_equivariant`: an equivariant rule sends `x` to an output fixed by the stabiliser of
  `x`.
* `exists_equivariant`: conversely, if every `x` has an admissible output fixed by its stabiliser,
  an equivariant rule with admissible outputs exists. Choose a representative in each orbit, an
  admissible fixed output for it, and carry it along the orbit; the stabiliser makes this well
  defined.
* `isotropy`: the two together.

No finiteness is needed; the representatives are chosen with `Classical.epsilon`.
-/

namespace Isotropy

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

variable (G) in
/-- Equivariance. -/
def Equivariant (f : X → Y) : Prop := ∀ (g : G) x, f (g • x) = g • f x

theorem fixed_of_equivariant {f : X → Y} (hf : Equivariant G f) {x : X} {g : G}
    (hg : g ∈ MulAction.stabilizer G x) : g • f x = f x := by
  rw [← hf g x, MulAction.mem_stabilizer_iff.mp hg]

variable (G) in
/-- A representative of the orbit of `x`, depending only on the orbit. -/
noncomputable def rep (x : X) : X :=
  @Classical.epsilon X ⟨x⟩ (fun z => z ∈ MulAction.orbit G x)

omit [MulAction G Y] in
lemma rep_mem (x : X) : rep G x ∈ MulAction.orbit G x :=
  Classical.epsilon_spec ⟨x, MulAction.mem_orbit_self x⟩

omit [MulAction G Y] in
lemma rep_smul (h : G) (x : X) : rep G (h • x) = rep G x := by
  unfold rep
  rw [MulAction.orbit_smul]

theorem exists_equivariant (A : X → Set Y)
    (hA : ∀ (g : G) (x : X) (y : Y), y ∈ A x → g • y ∈ A (g • x))
    (h : ∀ x, ∃ y ∈ A x, ∀ g ∈ MulAction.stabilizer G x, g • y = y) :
    ∃ f : X → Y, Equivariant G f ∧ ∀ x, f x ∈ A x := by
  choose y hyA hyfix using h
  have hr : ∀ x : X, ∃ g : G, g • rep G x = x := by
    intro x
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (rep_mem (G := G) x)
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  choose c hc using hr
  -- any element carrying the representative to `x` gives the same output
  have wd : ∀ (x : X) (g : G), g • rep G x = x → g • y (rep G x) = c x • y (rep G x) := by
    intro x g hg
    have hst : (g⁻¹ * c x) ∈ MulAction.stabilizer G (rep G x) := by
      rw [MulAction.mem_stabilizer_iff, mul_smul, hc x]
      exact inv_smul_eq_iff.mpr hg.symm
    have hfix := hyfix (rep G x) _ hst
    rw [mul_smul] at hfix
    calc g • y (rep G x) = g • (g⁻¹ • (c x • y (rep G x))) := by rw [hfix]
      _ = c x • y (rep G x) := smul_inv_smul g _
  refine ⟨fun x => c x • y (rep G x), ?_, ?_⟩
  · intro h x
    show c (h • x) • y (rep G (h • x)) = h • (c x • y (rep G x))
    have e1 : (h * c x) • rep G (h • x) = h • x := by rw [rep_smul, mul_smul, hc x]
    rw [← wd (h • x) (h * c x) e1, rep_smul, mul_smul]
  · intro x
    have hmem := hA (c x) (rep G x) (y (rep G x)) (hyA _)
    rwa [hc x] at hmem

/-- The isotropy lemma: an equivariant rule with admissible outputs exists exactly when every
input has an admissible output fixed by its stabiliser. -/
theorem isotropy (A : X → Set Y) (hA : ∀ (g : G) (x : X) (y : Y), y ∈ A x → g • y ∈ A (g • x)) :
    (∃ f : X → Y, Equivariant G f ∧ ∀ x, f x ∈ A x) ↔
      ∀ x, ∃ y ∈ A x, ∀ g ∈ MulAction.stabilizer G x, g • y = y := by
  constructor
  · rintro ⟨f, hf, hfA⟩ x
    exact ⟨f x, hfA x, fun g hg => fixed_of_equivariant hf hg⟩
  · exact exists_equivariant A hA

end Isotropy
