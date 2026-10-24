/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean -/

/-
Author: Muse Spark 1.3
-/

import sympy.atlas.Analysis.InnerProductSpace.NeumannPolyaBenchmark
import Lemma.Real.InnerProductSpace.NeumannPolyaBenchmark

open TopologicalSpace

namespace EuclideanLaplacianTest

example {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    EuclideanLaplacian.neumannPolyaEigenvalueBenchmark Ω j =
      (2 * Real.pi) ^ 2 *
        ((((j : ℕ) : ℝ) /
          (EuclideanLaplacian.unitBallVolume n *
            EuclideanLaplacian.domainVolume Ω)) ^ (2 / (n : ℝ))) :=
  rfl

example {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ EuclideanLaplacian.neumannPolyaEigenvalueBenchmark Ω j :=
  EuclideanLaplacian.neumannPolyaEigenvalueBenchmark_nonneg Ω j

example {n : ℕ} (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    EuclideanLaplacian.neumannPolyaEigenvalueBenchmark Ω (j + 1) =
      EuclideanLaplacian.polyaEigenvalueBenchmark Ω j :=
  EuclideanLaplacian.neumannPolyaEigenvalueBenchmark_succ Ω j

end EuclideanLaplacianTest
