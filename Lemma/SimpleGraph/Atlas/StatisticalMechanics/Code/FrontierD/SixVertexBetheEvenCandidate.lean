import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheEvenCandidate.Part4
open Finset StatMech StatMech.FrontierD


/--
[sixVertexFixedEvenChargeBetheParticleCount_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheParticleCount_eq_eq
  {s k : Nat} :
-- imply
  sixVertexFixedChargeBetheParticleCount (2 * s) k = (s + k + 1) + (s + k + 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheParticleCount_eq s k

/--
[sixVertexFixedEvenChargeBetheRoots_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheRoots_symmetric_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  SixVertexRootSymmetric (sixVertexFixedEvenChargeBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheRoots_symmetric hc s k

/--
[prod_sixVertexFixedEvenChargeBetheRoots](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma prod_sixVertexFixedEvenChargeBetheRoots_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c)
  (f : Real -> Complex) :
-- imply
  (∏ i, f (sixVertexFixedChargeBetheRoots hc (2 * s) k i)) = (∏ j, f (sixVertexFixedEvenPositiveBetheRoots hc s k j)) * ∏ j, f (-sixVertexFixedEvenPositiveBetheRoots hc s k j) := by
-- proof
  apply StatMech.FrontierD.prod_sixVertexFixedEvenChargeBetheRoots hc s k f

/--
[sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexFixedChargeBetheRoots hc (2 * s) k) = sixVertexSymmetricBetheEigenvalueCandidate c (sixVertexFixedEvenPositiveBetheRoots hc s k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_symmetric hc s k

/--
[sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheEigenvalueCandidate c (sixVertexFixedChargeBetheRoots hc (2 * s) k) = (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheEigenvalueCandidate_eq_value hc s k

/--
[sixVertexFixedEvenChargeBetheEigenvalueValue_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheEigenvalueValue_pos_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  0 < sixVertexFixedEvenChargeBetheEigenvalueValue hc s k := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheEigenvalueValue_pos hc s k

/--
[sixVertexFixedEvenChargeBetheRoots_eigenrelation_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheRoots_eigenrelation_value_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexSectorTransferComplex (sixVertexFourWidth (2 * s) k) (sixVertexFixedChargeBetheParticleCount (2 * s) k) c).mulVec (sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc (2 * s) k)) = (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k : Complex) • sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc (2 * s) k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheRoots_eigenrelation_value hc s k

/--
[sixVertexFixedEvenChargeBetheEigenvalueValue_log](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexFixedEvenChargeBetheEigenvalueValue_log_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Real.log (sixVertexFixedEvenChargeBetheEigenvalueValue hc s k) = Real.log 2 + 2 * ∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖ := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedEvenChargeBetheEigenvalueValue_log hc s k

/--
[sixVertexEvenChargeBetheCandidateLogRatio_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheEvenCandidate.lean)
-/
@[path]
private lemma sixVertexEvenChargeBetheCandidateLogRatio_eq_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexEvenChargeBetheCandidateLogRatio hc s k = 2 * ((∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexFixedEvenPositiveBetheRoots hc s k j))‖) - ∑ j, Real.log ‖sixVertexBetheM c (sixVertexBethePhase (sixVertexPositiveHalfBetheRoots hc (2 * s + k) j))‖) := by
-- proof
  apply StatMech.FrontierD.sixVertexEvenChargeBetheCandidateLogRatio_eq hc s k


-- created on 2026-10-23
