/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/InnerProductSpace/DirichletSpectrum.lean -/

/-
Author: Muse Spark 1.3
-/

import Def.Analysis.InnerProductSpace.DirichletSpectrum
import Lemma.Real.InnerProductSpace.DirichletSpectrum
open TopologicalSpace DirichletLaplacian MeasureTheory

/-!
# Tests for the variational Dirichlet spectrum bridge
-/


namespace DirichletLaplacianTest

variable {n : ℕ}

/-- `SmoothTestSpace` is the bundled smooth compactly supported test functions. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    SmoothTestSpace Ω = TestFunction Ω ℝ ⊤ :=
  rfl

/-- `rayleighQuotient` is the gradient-energy over mass ratio. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) (f : SmoothTestSpace Ω) :
    DirichletLaplacian.rayleighQuotient f =
      (∫ x, ‖fderiv ℝ (f : EuclideanSpace ℝ (Fin n) → ℝ) x‖ ^ 2 ∂volume) /
        (∫ x, |f x| ^ 2 ∂volume) :=
  rfl

/-- `variationalEigenvalue` is the min--max value at the given index. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    DirichletLaplacian.variationalEigenvalue Ω j =
      sInf {a : ℝ | ∃ V : Submodule ℝ (SmoothTestSpace Ω),
        Module.finrank ℝ ↥V = j + 1 ∧
          a = sSup {q : ℝ | ∃ f : ↥V,
            (f : SmoothTestSpace Ω) ≠ 0 ∧
              DirichletLaplacian.rayleighQuotient (f : SmoothTestSpace Ω) = q}} :=
  rfl

/-- `IsDirichletSpectrum` is pointwise equality with the variational sequence. -/
example (S : NonnegativeDiscreteSpectrum)
    (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    S.IsDirichletSpectrum Ω ↔
      ∀ j, S j = DirichletLaplacian.variationalEigenvalue Ω j :=
  Iff.rfl

/-- The zero test function has Rayleigh quotient `0`: both integrals vanish and
Lean's field division satisfies `0 / 0 = 0`. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    DirichletLaplacian.rayleighQuotient (0 : SmoothTestSpace Ω) = 0 := by
  unfold DirichletLaplacian.rayleighQuotient
  simp

/-- The spectrum relation unfolds pointwise at each index. -/
example (S : NonnegativeDiscreteSpectrum)
    (Ω : Opens (EuclideanSpace ℝ (Fin n)))
    (h : S.IsDirichletSpectrum Ω) (j : ℕ) :
    S j = DirichletLaplacian.variationalEigenvalue Ω j :=
  h j

/-- At `j = 0` the min--max ranges over one-dimensional submodules. This pins
the `j + 1` shift definitionally and asserts no numerical eigenvalue. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    DirichletLaplacian.variationalEigenvalue Ω 0 =
      sInf {a : ℝ | ∃ V : Submodule ℝ (SmoothTestSpace Ω),
        Module.finrank ℝ ↥V = 0 + 1 ∧
          a = sSup {q : ℝ | ∃ f : ↥V,
            (f : SmoothTestSpace Ω) ≠ 0 ∧
              DirichletLaplacian.rayleighQuotient (f : SmoothTestSpace Ω) = q}} :=
  rfl

end DirichletLaplacianTest

namespace EuclideanLaplacianTest

variable {n : ℕ}

/-- `unitBallVolume` is `volume.real` of the unit ball. -/
example (m : ℕ) :
    EuclideanLaplacian.unitBallVolume m =
      (volume : Measure (EuclideanSpace ℝ (Fin m))).real
        (Metric.ball (0 : EuclideanSpace ℝ (Fin m)) 1) :=
  rfl

/-- `domainVolume` is `volume.real` of the underlying set of `Ω`. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    EuclideanLaplacian.domainVolume Ω =
      (volume : Measure (EuclideanSpace ℝ (Fin n))).real (Ω : Set _) :=
  rfl

/-- `semiclassicalCountingCoefficient` unfolds exactly. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    EuclideanLaplacian.semiclassicalCountingCoefficient Ω =
      EuclideanLaplacian.unitBallVolume n * EuclideanLaplacian.domainVolume Ω /
        (2 * Real.pi) ^ n :=
  rfl

/-- `polyaEigenvalueBenchmark` unfolds exactly, visibly retaining `j + 1`. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    EuclideanLaplacian.polyaEigenvalueBenchmark Ω j =
      (2 * Real.pi) ^ 2 *
        ((((j + 1 : ℕ) : ℝ) /
          (EuclideanLaplacian.unitBallVolume n *
            EuclideanLaplacian.domainVolume Ω)) ^ (2 / (n : ℝ))) :=
  rfl

/-- At `j = 0` the benchmark uses the one-based first eigenvalue number. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    EuclideanLaplacian.polyaEigenvalueBenchmark Ω 0 =
      (2 * Real.pi) ^ 2 *
        (((1 : ℝ) /
          (EuclideanLaplacian.unitBallVolume n *
            EuclideanLaplacian.domainVolume Ω)) ^ (2 / (n : ℝ))) := by
  have h : ((0 + 1 : ℕ) : ℝ) = 1 := by norm_num
  unfold EuclideanLaplacian.polyaEigenvalueBenchmark
  rw [h]

/-- The unit-ball volume is nonnegative. -/
example (m : ℕ) : 0 ≤ EuclideanLaplacian.unitBallVolume m :=
  EuclideanLaplacian.unitBallVolume_nonneg m

/-- The domain volume is nonnegative. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    0 ≤ EuclideanLaplacian.domainVolume Ω :=
  EuclideanLaplacian.domainVolume_nonneg Ω

/-- The semiclassical counting coefficient is nonnegative. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) :
    0 ≤ EuclideanLaplacian.semiclassicalCountingCoefficient Ω :=
  EuclideanLaplacian.semiclassicalCountingCoefficient_nonneg Ω

/-- The eigenvalue benchmark is nonnegative. -/
example (Ω : Opens (EuclideanSpace ℝ (Fin n))) (j : ℕ) :
    0 ≤ EuclideanLaplacian.polyaEigenvalueBenchmark Ω j :=
  EuclideanLaplacian.polyaEigenvalueBenchmark_nonneg Ω j

end EuclideanLaplacianTest
