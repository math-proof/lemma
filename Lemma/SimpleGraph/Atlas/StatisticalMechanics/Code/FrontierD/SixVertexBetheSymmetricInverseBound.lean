import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSymmetricInverseBound
open Finset Matrix StatMech StatMech.FrontierD


/--
[exists_abs_le_scaledJacobian_mulVec_of_sourceBounds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricInverseBound.lean)
-/
@[path]
private lemma exists_abs_le_scaledJacobian_mulVec_of_sourceBounds_eq
  {N m : Nat}
  {c : Real}
  {q : Fin m -> Real}
  {eps M : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hq : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (G : Fin m -> Real)
  (heps : 0 <= eps)
  (hM : 0 <= M)
  (hmargin : M + 2 * eps < 2 * Real.pi)
  (hdiag : forall j, |sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j j - 2 * Real.pi| <= eps)
  (hoff : forall j, |(∑ k ∈ univ.erase j, sixVertexBethePositiveHalfScaledJacobianMatrix N m c q j k) - G j| <= eps)
  (hG : forall j, 0 <= G j /\ G j <= M)
  (v : Fin m -> Real) :
-- imply
  exists i, (forall j, |v j| <= |v i|) /\ (2 * Real.pi - M - 2 * eps) * := by
-- proof
  apply StatMech.FrontierD.exists_abs_le_scaledJacobian_mulVec_of_sourceBounds hc hm hq G eps M heps hM hmargin hdiag hoff hG v

/--
[exists_abs_le_scaledJacobian_mulVec_of_finiteDensityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSymmetricInverseBound.lean)
-/
@[path]
private lemma exists_abs_le_scaledJacobian_mulVec_of_finiteDensityLower_eq
  {c : Real}
  {N m : Nat}
  {q : Fin m -> Real}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hm : 0 < m)
  (hN : 0 < N)
  (hcount : m + m <= N)
  (hopen : SixVertexOpenRootSimplex (sixVertexEvenSymmetricLift m q))
  (hsol : SixVertexSatisfiesBetheEquations c N (m + m) (sixVertexEvenSymmetricLift m q))
  (hlower : 0 < lower)
  (hdensity : forall x, lower <= sixVertexFiniteRootDensity c N (m + m) (sixVertexEvenSymmetricLift m q) x)
  (hmargin : sixVertexSymmetricScatteringBoundaryBound c + 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower < 2 * Real.pi)
  (v : Fin m -> Real) :
-- imply
  exists i, (forall j, |v j| <= |v i|) /\ (2 * Real.pi - sixVertexSymmetricScatteringBoundaryBound c - 2 * sixVertexSymmetricJacobianTotalErrorOfLower c N lower) * := by
-- proof
  apply StatMech.FrontierD.exists_abs_le_scaledJacobian_mulVec_of_finiteDensityLower hc hm hN hcount hopen hsol hlower hdensity hmargin v


-- created on 2026-10-23
