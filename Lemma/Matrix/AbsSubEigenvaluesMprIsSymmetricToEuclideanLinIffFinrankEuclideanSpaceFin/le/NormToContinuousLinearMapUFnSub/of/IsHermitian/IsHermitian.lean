import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Analysis.InnerProductSpace.WeylPerturbation

/--
[WeylPerturbation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/WeylPerturbation.lean)
-/
@[path]
private lemma weyl_eigenvalue_perturbation_le
-- given
  {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℂ)
  (hA : A.IsHermitian)
  (hB : B.IsHermitian)
  (i : Fin n) :
-- imply
  |(Matrix.isSymmetric_toEuclideanLin_iff.mpr hA).eigenvalues finrank_euclideanSpace_fin i -
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr hB).eigenvalues finrank_euclideanSpace_fin i| ≤
    ‖(Matrix.toEuclideanLin (A - B)).toContinuousLinearMap‖ := by
-- proof
  apply InnerProductSpace.WeylPerturbationWanted.weyl_eigenvalue_perturbation_le A B hA hB i

-- created on 2026-10-10
