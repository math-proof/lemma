import Mathlib
import sympy.Basic
import Theorem.RingTheory.GradedAlgebra.MultigradedBaseChangedDifferential
open MetaMathlibExt


/--
[MultigradedFreeResolution.baseChangedDifferential_preservesDegree](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/MultigradedBaseChangedDifferential.lean)
-/
@[path]
private lemma MultigradedFreeResolution_baseChangedDifferential_preservesDegree_eq
  :
-- imply
  {K : Type u} [Field K] {n : ℕ}
    {M : Type u} [AddCommGroup M] [Module (MvPolynomial (Fin n) K) M]
    [Module K M]
    (targetGraded : MultigradedPolynomialModule K n M)
    (resolution : CategoryTheory.ProjectiveResolution
    (ModuleCat.of (MvPolynomial (Fin n) K) M))
    (ι : ℕ → Type u)
    (res : MultigradedFreeResolution K n M targetGraded resolution ι)
    (i : ℕ) (α : Fin n →₀ Int)
    (x : ↥((baseChangedComplex (K := by
-- proof
  apply MetaMathlibExt.MultigradedFreeResolution.baseChangedDifferential_preservesDegree


-- created on 2026-10-20
