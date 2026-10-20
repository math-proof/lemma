import Mathlib
import sympy.Basic
import sympy.atlas.RingTheory.GradedAlgebra.FiniteHomogeneousGenerators
open MetaMathlibExt


/--
[MultigradedPolynomialModule.exists_finset_homogeneous_generators](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/GradedAlgebra/FiniteHomogeneousGenerators.lean)
-/
@[path]
private lemma MultigradedPolynomialModule_exists_finset_homogeneous_generators_eq
  [Field K] [AddCommGroup M] [Module K M]
  {n : ℕ} [Module (MvPolynomial (Fin n) K) M] [Module.Finite (MvPolynomial (Fin n) K) M]
  {targetGraded : MultigradedPolynomialModule K n M} :
-- imply
  ∃ s : Finset M,
    (∀ m ∈ s, ∃ α : Fin n →₀ Int, m ∈ targetGraded.component α) ∧
    Submodule.span (MvPolynomial (Fin n) K) (s : Set M) = ⊤ := by
-- proof
  apply MetaMathlibExt.MultigradedPolynomialModule.exists_finset_homogeneous_generators K n M targetGraded


-- created on 2026-10-20
