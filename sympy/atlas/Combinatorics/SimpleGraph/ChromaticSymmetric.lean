/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/ChromaticSymmetric.lean -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# Chromatic symmetric functions via coloring profiles

The chromatic symmetric function of a graph is determined by the counts of
proper colorings with each multiplicity profile: for every finite labeled
palette and every prescribed multiplicity of each color, count the proper
colorings realizing exactly those multiplicities. This module packages those
counts (`chromaticProfileCount`) and the resulting notion of two graphs having
the same chromatic symmetric function (`SameChromaticSymmetricFunction`),
together with its basic equivalence and isomorphism-invariance interface.
-/

namespace SimpleGraph

variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

/-- Number of proper colorings of `G` with labeled colors `Fin k` in which
each color occurs with exactly the prescribed multiplicity. These counts are
the coefficients of the chromatic symmetric function. -/
noncomputable def chromaticProfileCount [Finite V] (G : SimpleGraph V) (k : ℕ)
    (multiplicity : Fin k → ℕ) : ℕ :=
  Nat.card { c : G.Coloring (Fin k) //
    ∀ color, Nat.card { v : V // c v = color } = multiplicity color }

/-- Equality of chromatic symmetric functions, represented transparently
through the coefficient characterization: agreement of all coloring-profile
counts for every finite palette and multiplicity profile. -/
def SameChromaticSymmetricFunction [Finite V] [Finite W]
    (G : SimpleGraph V) (H : SimpleGraph W) : Prop :=
  ∀ k multiplicity,
    chromaticProfileCount G k multiplicity = chromaticProfileCount H k multiplicity

/-- Every graph has the same chromatic symmetric function as itself. -/
theorem SameChromaticSymmetricFunction.refl [Finite V] (G : SimpleGraph V) :
    SameChromaticSymmetricFunction G G :=
  fun _ _ => rfl

/-- Symmetry of chromatic-symmetric-function equality. -/
theorem SameChromaticSymmetricFunction.symm
    [Finite V] [Finite W]
    (h : SameChromaticSymmetricFunction G H) : SameChromaticSymmetricFunction H G :=
  fun k multiplicity => (h k multiplicity).symm

/-- Transitivity of chromatic-symmetric-function equality. -/
theorem SameChromaticSymmetricFunction.trans [Finite V] [Finite W]
    {U : Type*} [Finite U] {K : SimpleGraph U}
    (hGH : SameChromaticSymmetricFunction G H)
    (hHK : SameChromaticSymmetricFunction H K) : SameChromaticSymmetricFunction G K :=
  fun k multiplicity => (hGH k multiplicity).trans (hHK k multiplicity)

/-- Isomorphic graphs have equal chromatic symmetric functions: colorings and
their color-class fibers transport along the isomorphism. -/
theorem SameChromaticSymmetricFunction.of_iso [Finite V] [Finite W] (e : G ≃g H) :
    SameChromaticSymmetricFunction G H := by
  intro k multiplicity
  classical
  let F : G.Coloring (Fin k) → H.Coloring (Fin k) := fun c => c.comap e.symm.toHom
  let B : H.Coloring (Fin k) → G.Coloring (Fin k) := fun d => d.comap e.toHom
  have hBF : ∀ c, B (F c) = c := fun c => by
    ext v
    simp [F, B, Coloring.comap]
  have hFB : ∀ d, F (B d) = d := fun d => by
    ext w
    simp [F, B, Coloring.comap]
  have hfib : ∀ (c : G.Coloring (Fin k)) (color : Fin k),
      Nat.card { w : W // F c w = color } = Nat.card { v : V // c v = color } := by
    intro c color
    apply Nat.card_congr
    refine
      { toFun := fun w => ⟨e.symm w, w.property⟩
        invFun := fun v => ⟨e v, by simpa [F, Coloring.comap] using v.property⟩
        left_inv := fun w => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  apply Nat.card_congr
  refine Equiv.subtypeEquiv ⟨F, B, hBF, hFB⟩ (fun c => ?_)
  simp only [Equiv.coe_fn_mk]
  constructor
  · intro h color
    rw [hfib c color]
    exact h color
  · intro h color
    rw [← hfib c color]
    exact h color

end SimpleGraph
