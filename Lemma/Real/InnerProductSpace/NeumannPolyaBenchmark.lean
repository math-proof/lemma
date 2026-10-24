import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.InnerProductSpace.NeumannPolyaBenchmark
open TopologicalSpace
open EuclideanLaplacian


namespace EuclideanLaplacian

/--
[neumannPolyaEigenvalueBenchmark_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean)
-/
@[path]
lemma neumannPolyaEigenvalueBenchmark_nonneg
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  0 ≤ neumannPolyaEigenvalueBenchmark Ω j := by
-- proof
  unfold neumannPolyaEigenvalueBenchmark
  exact mul_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) 2)
    (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))) _)
/-- The source's Neumann index `j + 2` has the same Weyl benchmark as the
Dirichlet index `j + 1`; in zero-based API indices this is `j + 1` versus `j`. -/
@[simp] theorem neumannPolyaEigenvalueBenchmark_succ {n : ℕ}
  (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
  neumannPolyaEigenvalueBenchmark Ω (j + 1) =
    polyaEigenvalueBenchmark Ω j :=
  rfl

end EuclideanLaplacian

/--
[neumannPolyaEigenvalueBenchmark_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean)
-/
@[path]
private lemma neumannPolyaEigenvalueBenchmark_succ_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  neumannPolyaEigenvalueBenchmark Ω (j + 1) =
    polyaEigenvalueBenchmark Ω j := by
-- proof
  apply EuclideanLaplacian.neumannPolyaEigenvalueBenchmark_succ Ω j


-- created on 2026-10-20
-- updated on 2026-10-23
