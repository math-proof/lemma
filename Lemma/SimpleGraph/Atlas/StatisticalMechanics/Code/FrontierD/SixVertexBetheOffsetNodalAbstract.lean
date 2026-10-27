import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetNodalAbstract
open StatMech StatMech.FrontierD


/--
[abs_densityOffset_sub_continuous_le_of_data](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalAbstract.lean)
-/
@[path]
private lemma abs_densityOffset_sub_continuous_le_of_data_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {rho eps : Fin n -> Real}
  {a : Real}
  {tau : Real -> Real}
  {aligned : Fin n -> Real}
  {boundary residual : Fin n -> Real}
  {rowBound reciprocalMass residualError boundaryError sourceMoveError testError : Real}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : 0 < n)
  (ha : 0 <= a)
  (hrho : forall j, 0 < rho j)
  (hpIcc : forall j, p j ∈ Set.Icc (-Real.pi) Real.pi)
  (hmass : (1 / (N : Real)) * ∑ j, (rho j * eps j - a * tau (p j)) / (sixVertexRootDensityWeight c (p j) * rho j) = 0)
  (hrow : forall i, (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) / rho j <= rowBound)
  (hreciprocal : reciprocalMass <= (1 / (N : Real)) * ∑ j, 1 / (sixVertexRootDensityWeight c (p j) * rho j))
  (hlinear : forall i, 2 * Real.pi * (rho i * eps i) + (1 / (N : Real)) * ∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) * eps j = residual i + boundary i)
  (hresidual : forall i, |residual i| <= residualError)
  (hboundary : forall i, |boundary i - a * sixVertexContinuousOffsetSource c (aligned i)| <= boundaryError)
  (hsourceMove : forall i, |a * (sixVertexContinuousOffsetSource c (aligned i) - sixVertexContinuousOffsetSource c (p i))| <= sourceMoveError)
  (hquad : forall i, |(∑ j, sixVertexContinuousOffsetKernel c (p i) (p j) * tau (p j) / rho j) / N - ∫ y in -Real.pi..Real.pi, sixVertexContinuousOffsetKernel c (p i) y * tau y| <= testError)
  (htauEq : SixVertexSatisfiesContinuousOffsetEquation c tau)
  (hmargin : 0 < 2 * Real.pi - (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) :
-- imply
  |rho i * eps i - a * tau (p i)| <= (residualError + boundaryError + sourceMoveError + a * testError) / (2 * Real.pi - (rowBound - sixVertexRootDensityKernelFloor c * reciprocalMass)) := by
-- proof
  apply StatMech.FrontierD.abs_densityOffset_sub_continuous_le_of_data hc hN hn ha hrho hpIcc hmass hrow hreciprocal hlinear hresidual hboundary hsourceMove hquad htauEq hmargin i

/--
[reciprocalWeightDensityMass_le_of_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetNodalAbstract.lean)
-/
@[path]
private lemma reciprocalWeightDensityMass_le_of_lower_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n -> Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hnN : n <= N)
  (hquarter : N <= 4 * n)
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N n p x) :
-- imply
  sixVertexRootDensityScale c / (4 * (sixVertexAnisotropyMagnitude c + 1) * sixVertexFiniteRootDensityUniformBound c) <= (1 / (N : Real)) * ∑ j, 1 / (sixVertexRootDensityWeight c (p j) * sixVertexFiniteRootDensity c N n p (p j)) := by
-- proof
  apply StatMech.FrontierD.reciprocalWeightDensityMass_le_of_lower hc hN hnN hquarter hlower hdensity


-- created on 2026-10-23
