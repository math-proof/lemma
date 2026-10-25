/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBetti.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Dimension.Finite
import Def.RingTheory.GradedAlgebra.MultigradedBetti
/-!
# Multigraded Betti numbers after residue-field base change

This file encodes multigraded Betti numbers via base change of an edge-2
graded free resolution along the canonical augmentation.

Source: Benjamin Braun and Brian Davis, “Antichain Simplices,”
Journal of Integer Sequences 23 (2020),
`https://cs.uwaterloo.ca/journals/JIS/VOL23/Braun/braun4.tex`,
exact lines 868–873. Those lines say that, for a graded free resolution `F`
of `M`, `β^R_(i,α)(M)` is the vector-space dimension of the `i`th homology
of the degree-`α` component of `K ⊗_R F`.

Deliberately deferred (not claimed here): Poincaré series, finite support
across degrees, eventual vanishing, and polynomiality. This file only
provides the augmentation, the actual base-changed complex, the degree
pieces with their certified decomposition and component complexes, and the
Betti number as the resulting `Module.finrank`.

Main definitions:

* `MetaMathlibExt.zeroEval`: the canonical augmentation
  `MvPolynomial (Fin n) K →+* K` evaluating every variable at zero.
* `MetaMathlibExt.baseChangedComplex`: the actual base-changed chain complex
  obtained from the edge-2 resolution by `ModuleCat.extendScalars`.
* `MetaMathlibExt.baseChangedDegreePiece`: degree pieces spanned by the
  actual base-changed homogeneous basis vectors.
* `MetaMathlibExt.MultigradedBaseChange`: certified direct-sum decomposition
  and restricted component complexes with injective inclusions, homology,
  and finite-dimensionality certificates.
* `MetaMathlibExt.multigradedBettiNumber`: the multigraded Betti number as
  the resulting `Module.finrank`.
-/


namespace MetaMathlibExt

universe u

/-- Certified base-change data over the canonical span family: one shared
direct-sum decomposition and successor-differential preservation, plus for
every multidegree the component complex with inclusion into the actual
base-changed complex, homology existence, and coefficientwise finiteness. -/
structure MultigradedBaseChange {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι) where
  /-- Direct-sum decomposition of each base-changed term over the degree pieces. -/
  decomposition : ∀ (i : ℕ), DirectSum.Decomposition
    (fun β => baseChangedDegreePiece targetGraded resolution ι res i β)
  /-- Successor differentials preserve each degree piece. -/
  diffPreserves : ∀ (i : ℕ) (β : Fin n →₀ Int)
    (x : ↥((baseChangedComplex resolution).X (i + 1))),
    x ∈ baseChangedDegreePiece targetGraded resolution ι res (i + 1) β →
      (ModuleCat.Hom.hom ((baseChangedComplex resolution).d (i + 1) i)) x ∈
        baseChangedDegreePiece targetGraded resolution ι res i β
  /-- Component complex for a fixed multidegree `α`. -/
  comp : (α : Fin n →₀ Int) →
    HomologicalComplex (ModuleCat.{u, u} K) (ComplexShape.down ℕ)
  /-- Inclusion of the `α` component complex into the base-changed complex. -/
  incl : ∀ (α : Fin n →₀ Int), HomologicalComplex.Hom (comp α)
    (baseChangedComplex resolution)
  /-- Each inclusion map is injective. -/
  incl_injective :
    ∀ (α : Fin n →₀ Int) (i : ℕ),
      Function.Injective ⇑(ModuleCat.Hom.hom ((incl α).f i))
  /-- The range of each inclusion is exactly the corresponding degree piece. -/
  range_eq : ∀ (α : Fin n →₀ Int) (i : ℕ),
    LinearMap.range (ModuleCat.Hom.hom ((incl α).f i)) =
      baseChangedDegreePiece targetGraded resolution ι res i α
  /-- Each component complex has homology at every index. -/
  hasHom : ∀ (α : Fin n →₀ Int) (i : ℕ),
    HomologicalComplex.HasHomology (comp α) i
  /-- Each component homology is finite-dimensional over `K`. -/
  finiteDim : ∀ (α : Fin n →₀ Int) (i : ℕ)
    [HomologicalComplex.HasHomology (comp α) i],
    Module.Finite K ↥(HomologicalComplex.homology (comp α) i)

end MetaMathlibExt
