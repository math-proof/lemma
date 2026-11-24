module
public import Def.Analysis.InnerProductSpace.DirichletSpectrum
public import Theorem.Real.InnerProductSpace.DirichletSpectrum
open TopologicalSpace


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean -/
/-
Author: Muse Spark 1.3
-/
namespace EuclideanLaplacian

/-- Zero-based Neumann Pólya benchmark. The numerator `j` corresponds to
the source's one-based eigenvalue number minus one, so index zero records the
constant Neumann mode in positive dimension. -/
noncomputable def neumannPolyaEigenvalueBenchmark {n : ℕ}
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    ((((j : ℕ) : ℝ) /
      (unitBallVolume n * domainVolume Ω)) ^ (2 / (n : ℝ)))

end EuclideanLaplacian
