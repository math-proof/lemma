import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheTailApproximateFixedPoint
open StatMech StatMech.FrontierD


/--
[abs_finiteRootDensity_continuousEquationResidual_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheTailApproximateFixedPoint.lean)
-/
@[path]
private lemma abs_finiteRootDensity_continuousEquationResidual_le_tail_eq :
-- imply
  ∀ {c : Real} (hc : 2 < c) (htail : 2 < sixVertexAnisotropyMagnitude c) {N n : Nat} (hN : 0 < N) (hhalf : N = 2 * (n + 1)) {p : Fin (n + 1) → Real} (hopen : SixVertexOpenRootSimplex p) (hsol : SixVertexSatisfiesBetheEquations c N (n + 1) p) (x : Real), |sixVertexRootDensityWeight c x * sixVertexFiniteRootDensity c N (n + 1) p x - (sixVertexRootDensityWeight c x / (2 * Real.pi) - (1 / (2 * Real.pi)) * ∫ y in -Real.pi..Real.pi, sixVertexRootDensityKernel c x y * sixVertexFiniteRootDensity c N (n + 1) p y)| <= (sixVertexRootDensityKernelLipschitzBound c * sixVertexFiniteRootDensityUniformBound c * (1 / ((N : Real) * sixVertexTailFiniteDensityFloor c)) * (2 * Real.pi)) / (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_finiteRootDensity_continuousEquationResidual_le_tail


-- created on 2026-10-23
