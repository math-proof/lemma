import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWConnectorTwoChannelFibreCube.Part3
open Finset SimpleGraph Set StatMech StatMech.Universality


/--
[rlc_twoChannelConfigOfVisibleFixed_variable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean)
-/
@[path]
private lemma rlc_twoChannelConfigOfVisibleFixed_variable_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {base : RlcTwoChannelPIMSVisibleBase gamma gamma'}
  {bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma')}
  {e : RlcTwoChannelPIMSVariableTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelConfigOfVisibleFixed base bits e.1 = base e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelConfigOfVisibleFixed_variable base bits e

/--
[rlc_twoChannelConfigOfVisibleFixed_fixed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean)
-/
@[path]
private lemma rlc_twoChannelConfigOfVisibleFixed_fixed_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {base : RlcTwoChannelPIMSVisibleBase gamma gamma'}
  {bits : ConfigSpace (RlcTwoChannelPIMSFixedTargetEdge gamma gamma')}
  {e : RlcTwoChannelPIMSFixedTargetEdge gamma gamma'} :
-- imply
  rlc_twoChannelConfigOfVisibleFixed base bits e.1 = bits e := by
-- proof
  apply StatMech.Universality.rlc_twoChannelConfigOfVisibleFixed_fixed base bits e

/--
[rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean)
-/
@[path]
private lemma rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {rho : RlcTwoChannelEdgeFailure gamma gamma'}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  rlc_twoChannelConfigOfVisibleFixed (rlc_twoChannelFailureVisibleBase hclosure rho) (rlc_twoChannelFailureComplementFixedBits rho) = rlc_twoChannelFullPIMSConfig gamma gamma' rho.1 := by
-- proof
  apply StatMech.Universality.rlc_twoChannelConfigOfFailureComplement_eq_fullPIMS hclosure rho

/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPIMSPhysicalSuccess](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPIMSPhysicalSuccess_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma')
  (hphysical : RlcTwoChannelFullPIMSPhysicalSuccess gamma gamma') :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_of_fullPIMSPhysicalSuccess hclosure hphysical

/--
[rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_fixedPayload](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWConnectorTwoChannelFibreCube.lean)
-/
@[path]
private lemma rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_fixedPayload_eq
  {n : Int}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
-- given
  (hclosure : RlcTwoChannelClosureFailureCertificate gamma gamma') :
-- imply
  RlcTwoChannelPIMSPooledVisibleFibreCapacity hclosure ↔ forall base : RlcTwoChannelPIMSVisibleBase gamma gamma', Fintype.card (RlcTwoChannelFailureVisibleFibre hclosure base) <= Fintype.card (RlcTwoChannelSuccessFixedPayload base) := by
-- proof
  apply StatMech.Universality.rlc_twoChannelPIMSPooledVisibleFibreCapacity_iff_fixedPayload hclosure


-- created on 2026-10-23
