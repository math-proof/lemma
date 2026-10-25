import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.RSWContactFreeAxisBridge.Part2
open Function MeasureTheory Set StatMech StatMech.Universality


/--
[rlc_mixedWiredConnectorEvent_of_axisGapOpen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_of_axisGapOpen_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hopen : ∀ t : ℤ, G.lower ≤ t -> t < G.upper -> omega s(![0, t], ![0, t + 1]) = true) :
-- imply
  omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_of_axisGapOpen G hn hlt omega hopen

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hclosed : RlcAxisGapPIMSPreimagesClosed G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed G hn hlt omega hclosed

/--
[rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean)
-/
@[path]
private lemma rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
  {omega : ConfigSpace (Sym2 (Site 2))}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcert : RlcAxisOrContactDualConnectorCertificate G omega) :
-- imply
  rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact G hn hlt omega hcert

/--
[rlc_mixedWiredConnector_half_of_axisOrContact](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean)
-/
@[path]
private lemma rlc_mixedWiredConnector_half_of_axisOrContact_eq
  {n : ℤ}
  {gamma : RlcRightDiagonalPath n}
  {gamma' : RlcLeftDiagonalPath n}
  {G : RlcAxisBarrierGap gamma gamma'}
-- given
  (hn : 0 < n)
  (hlt : G.lower + 1 < G.upper)
  (hcert : ∀ omega : ConfigSpace (Sym2 (Site 2)), omega ∉ rlc_mixedWiredConnectorEvent G -> RlcAxisOrContactDualConnectorCertificate G omega) :
-- imply
  (1 : ℝ) / 2 ≤ rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
-- proof
  apply StatMech.Universality.rlc_mixedWiredConnector_half_of_axisOrContact G hn hlt hcert

/--
[rlc_windingSideCounterexample_contactFree_dual_success](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean)
-/
@[path]
private lemma rlc_windingSideCounterexample_contactFree_dual_success_eq :
-- imply
  rlc_windingSideCounterexampleConfig ∉ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧ ¬ RlcLowestHighestReflectedBoundaryContact rlc_windingSideCounterexampleGap rlc_windingSideCounterexampleConfig ∧ rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈ rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
-- proof
  apply StatMech.Universality.rlc_windingSideCounterexample_contactFree_dual_success


-- created on 2026-10-23
