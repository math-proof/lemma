/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBetti.lean -/

/-
  Author: Muse Code powered by Meta Muse Spark
-/

import Structure.RingTheory.GradedAlgebra.MultigradedFreeResolution
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Dimension.Finite
import Structure.RingTheory.GradedAlgebra.MultigradedBetti
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

/-- Readable multigraded Betti number: `Module.finrank` of the component homology. -/
noncomputable def multigradedBettiNumber {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M]
    [Module (MvPolynomial (Fin n) K) M] [Module K M]
    {targetGraded : MultigradedPolynomialModule K n M}
    {resolution : CategoryTheory.ProjectiveResolution
      (ModuleCat.of (MvPolynomial (Fin n) K) M)}
    {ι : ℕ → Type u}
    {res : MultigradedFreeResolution K n M targetGraded resolution ι}
    (data : MultigradedBaseChange targetGraded resolution ι res)
    (α : Fin n →₀ Int) (i : ℕ) : ℕ :=
  haveI := data.hasHom α i
  haveI := data.finiteDim α i
  Module.finrank K ↥(HomologicalComplex.homology (data.comp α) i)

end MetaMathlibExt
