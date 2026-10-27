import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheOffsetJacobianResidual
open Finset Matrix StatMech StatMech.FrontierD


/--
[sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetJacobianResidual.lean)
-/
@[path]
private lemma sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator_eq
  {N n : Nat}
  {c : Real}
  {j : Fin n}
-- given
  (hN : 0 < N)
  (q eps : Fin n -> Real) :
-- imply
  (sixVertexBetheJacobianMatrix N n c q).mulVec eps j / N = eps j + (1 / (N : Real)) * ∑ l, ((4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q l) / sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps j + (-4 * sixVertexDelta c * sixVertexBetheIntegratingFactor c (q j) / sixVertexThetaDerivativeDenominator c (q j) (q l)) * eps l) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheJacobianMatrix_mulVec_div_eq_linearizedNodalOperator hN c q eps j

/--
[sixVertexEvenChargeOffsetNodalResidual_eq_jacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetJacobianResidual.lean)
-/
@[path]
private lemma sixVertexEvenChargeOffsetNodalResidual_eq_jacobian_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeOffsetNodalResidual hc s k j = (sixVertexBetheJacobianMatrix (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) c (sixVertexFixedChargeBetheRoots hc (2 * s) k)).mulVec (sixVertexEvenChargeBetheOffset hc s k) j / sixVertexFourWidth (2 * s) k - sixVertexEvenChargeOffsetBoundarySource hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeOffsetNodalResidual_eq_jacobian hc s k j

/--
[sixVertexOddChargeOffsetNodalResidual_eq_jacobian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetJacobianResidual.lean)
-/
@[path]
private lemma sixVertexOddChargeOffsetNodalResidual_eq_jacobian_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexOddChargeOffsetNodalResidual hc s k j = (sixVertexBetheJacobianMatrix (sixVertexFourWidth (2 * s + 1) k) (sixVertexFixedChargeBetheParticleCount (2 * s + 1) k) c (sixVertexFixedChargeBetheRoots hc (2 * s + 1) k)).mulVec (sixVertexOddChargeBetheOffset hc s k) j / sixVertexFourWidth (2 * s + 1) k - sixVertexOddChargeOffsetBoundarySource hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexOddChargeOffsetNodalResidual_eq_jacobian hc s k j

/--
[sixVertexEvenChargeAlignedHalfRoots_rev](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheOffsetJacobianResidual.lean)
-/
@[path]
private lemma sixVertexEvenChargeAlignedHalfRoots_rev_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (sixVertexFixedChargeBetheParticleCount (2 * s) k)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeAlignedHalfRoots hc s k j.rev = -sixVertexEvenChargeAlignedHalfRoots hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeAlignedHalfRoots_rev hc s k j


-- created on 2026-10-23
