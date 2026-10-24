import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.InnerProductSpace.DirichletSpectrum
open TopologicalSpace MeasureTheory
open EuclideanLaplacian


namespace EuclideanLaplacian

/--
[unitBallVolume_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
lemma unitBallVolume_nonneg
  {n : ℕ} :
-- imply
  0 ≤ unitBallVolume n :=
-- proof
  measureReal_nonneg

end EuclideanLaplacian

namespace EuclideanLaplacian

/--
[domainVolume_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
lemma domainVolume_nonneg
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))} :
-- imply
  0 ≤ domainVolume Ω :=
-- proof
  measureReal_nonneg

end EuclideanLaplacian

namespace EuclideanLaplacian

/--
[semiclassicalCountingCoefficient_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
lemma semiclassicalCountingCoefficient_nonneg
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))} :
-- imply
  0 ≤ semiclassicalCountingCoefficient Ω := by
-- proof
  unfold semiclassicalCountingCoefficient
  exact div_nonneg
    (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) n)

end EuclideanLaplacian

namespace EuclideanLaplacian

/--
[polyaEigenvalueBenchmark_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/DirichletSpectrum.lean)
-/
@[path]
lemma polyaEigenvalueBenchmark_nonneg
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  0 ≤ polyaEigenvalueBenchmark Ω j := by
-- proof
  unfold polyaEigenvalueBenchmark
  exact mul_nonneg
    (pow_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg) 2)
    (Real.rpow_nonneg
      (div_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (unitBallVolume_nonneg n) (domainVolume_nonneg Ω))) _)

end EuclideanLaplacian


-- created on 2026-10-20
-- updated on 2026-10-23
