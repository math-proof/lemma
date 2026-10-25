/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWContactFreeAxisBridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Universality.RSWExtremalSelectionObstruction
import Def.StatisticalMechanics.Code.Universality.RSWContactFreeAxisBridge.Part2
open Function MeasureTheory Set


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box


theorem rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hcert : RlcAxisOrContactDualConnectorCertificate G omega) :
    rlc_dualReflectConfig omega ∈ rlc_mixedWiredConnectorEvent G := by
  rcases hcert with haxis | ⟨hcontact, horder⟩
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed
      G hn hlt omega haxis
  · exact rlc_mixedWiredConnectorEvent_dualReflect_of_boundaryContact
      G hn hlt omega hcontact horder


theorem rlc_mixedWiredConnector_half_of_axisOrContact
    {n : ℤ} {gamma : RlcRightDiagonalPath n}
    {gamma' : RlcLeftDiagonalPath n}
    (G : RlcAxisBarrierGap gamma gamma') (hn : 0 < n)
    (hlt : G.lower + 1 < G.upper)
    (hcert : ∀ omega : ConfigSpace (Sym2 (Site 2)),
      omega ∉ rlc_mixedWiredConnectorEvent G ->
        RlcAxisOrContactDualConnectorCertificate G omega) :
    (1 : ℝ) / 2 ≤
      rba_selfDualMeasure.real (rlc_mixedWiredConnectorEvent G) := by
  apply rlc_mixedWiredConnector_half_of_dual_reflection G
  intro omega hno
  exact rlc_mixedWiredConnectorEvent_dualReflect_of_axisOrContact
    G hn hlt omega (hcert omega hno)


theorem rlc_windingSideCounterexample_contactFree_dual_success :
    rlc_windingSideCounterexampleConfig ∉
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap ∧
      ¬ RlcLowestHighestReflectedBoundaryContact
        rlc_windingSideCounterexampleGap
        rlc_windingSideCounterexampleConfig ∧
      rlc_dualReflectConfig rlc_windingSideCounterexampleConfig ∈
        rlc_mixedWiredConnectorEvent rlc_windingSideCounterexampleGap := by
  refine ⟨rlc_windingSideCounterexample_failure,
    rlc_windingSideCounterexample_not_reflectedBoundaryContact, ?_⟩
  apply rlc_mixedWiredConnectorEvent_dualReflect_of_axisGapPreimagesClosed
    rlc_windingSideCounterexampleGap (by norm_num)
      (by change (-1 : ℤ) + 1 < 1; omega)
  unfold RlcAxisGapPIMSPreimagesClosed
  intro t htLower htUpper
  rfl

end Universality
end StatMech
