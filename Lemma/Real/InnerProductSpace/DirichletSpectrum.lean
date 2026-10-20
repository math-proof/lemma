import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.InnerProductSpace.DirichletSpectrum
open TopologicalSpace MeasureTheory
open EuclideanLaplacian


/--
[unitBallVolume_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
private lemma unitBallVolume_nonneg_eq
  {n : ℕ} :
-- imply
  0 ≤ unitBallVolume n := by
-- proof
  apply EuclideanLaplacian.unitBallVolume_nonneg n

/--
[domainVolume_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
private lemma domainVolume_nonneg_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))} :
-- imply
  0 ≤ domainVolume Ω := by
-- proof
  apply EuclideanLaplacian.domainVolume_nonneg Ω

/--
[semiclassicalCountingCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
private lemma semiclassicalCountingCoefficient_nonneg_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))} :
-- imply
  0 ≤ semiclassicalCountingCoefficient Ω := by
-- proof
  apply EuclideanLaplacian.semiclassicalCountingCoefficient_nonneg Ω

/--
[polyaEigenvalueBenchmark_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
private lemma polyaEigenvalueBenchmark_nonneg_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  0 ≤ polyaEigenvalueBenchmark Ω j := by
-- proof
  apply EuclideanLaplacian.polyaEigenvalueBenchmark_nonneg Ω j


-- created on 2026-10-20
