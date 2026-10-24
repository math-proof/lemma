import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetDiscreteStability
open StatMech StatMech.FrontierD


/--
[discreteOffsetError_le_of_zeroMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetDiscreteStability.lean)
-/
@[path]
private lemma discreteOffsetError_le_of_zeroMass_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {rho e : Fin n -> Real}
  {eta rowBound reciprocalMass : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : 0 < n)
  (hrho : forall j, 0 < rho j)
  (hmass : (1 / (N : Real)) * ∑ j, e j / (sixVertexRootDensityWeight c (p j) * rho j) = 0)
  (hrow : forall i, (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / rho j <= rowBound)
  (hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ j, 1 / (sixVertexRootDensityWeight c (p j) * rho j))
  (hdefect : forall i, |2 * Real.pi * e i + (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / rho j * e j| <= eta)
  (hmargin : 0 < 2 * Real.pi - (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) :
-- imply
  forall i, := by
-- proof
  apply StatMech.FrontierD.discreteOffsetError_le_of_zeroMass hc hN hn hrho hmass hrow hreciprocal hdefect hmargin


-- created on 2026-10-23
