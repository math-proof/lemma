/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean -/

/-
Author: Muse Spark 1.3
-/

import sympy.atlas.Analysis.InnerProductSpace.DirichletSpectrum
open TopologicalSpace

namespace EuclideanLaplacian

/-- Zero-based Neumann Pólya benchmark. The numerator `j` corresponds to
the source's one-based eigenvalue number minus one, so index zero records the
constant Neumann mode in positive dimension. -/
noncomputable def neumannPolyaEigenvalueBenchmark {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((((j : ℕ) : ℝ) /
      (unitBallVolume n * domainVolume Ω)) ^ (2 / (n : ℝ)))

theorem neumannPolyaEigenvalueBenchmark_nonneg {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ neumannPolyaEigenvalueBenchmark Ω j := by
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
