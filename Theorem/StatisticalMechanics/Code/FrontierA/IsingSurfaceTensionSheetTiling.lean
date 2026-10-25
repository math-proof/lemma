/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionSheetTiling.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionSheetPositionReduction
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeInfiniteVolume.Part7
open Finset
open scoped BigOperators symmDiff


namespace StatMech.FrontierA

noncomputable section

theorem gaugeWilsonExpectation_prod_boundary_le_biUnion
    {I E P : Type*} [Fintype E] [DecidableEq E]
    [Fintype P] [DecidableEq P] [DecidableEq I]
    (incidence : P -> Finset E) (K : P -> Real) (hK : forall p, 0 < K p)
    (S : Finset I) (D : I -> Finset P)
    (hdisj : forall i, i ∈ S -> forall j, j ∈ S -> i ≠ j ->
      Disjoint (D i) (D j)) :
    (∏ i ∈ S, gaugeWilsonExpectation incidence K
        (gaugeSurfaceBoundary incidence (D i))) <=
      gaugeWilsonExpectation incidence K
        (gaugeSurfaceBoundary incidence (S.biUnion D)) := by
  induction S using Finset.induction_on with
  | empty =>
      simp [gaugeSurfaceBoundary, plaquetteIncidenceCount,
        gaugeWilsonExpectation_empty]
  | @insert i S hi ih =>
      have hrest : forall j, j ∈ S -> forall k, k ∈ S -> j ≠ k ->
          Disjoint (D j) (D k) := by
        intro j hj k hk hjk
        exact hdisj j (Finset.mem_insert_of_mem hj) k
          (Finset.mem_insert_of_mem hk) hjk
      have hsurface : Disjoint (D i) (S.biUnion D) := by
        rw [Finset.disjoint_biUnion_right]
        intro j hj
        exact hdisj i (Finset.mem_insert_self i S) j
          (Finset.mem_insert_of_mem hj) (by aesop)
      have hi_nonneg : 0 <= gaugeWilsonExpectation incidence K
          (gaugeSurfaceBoundary incidence (D i)) :=
        (gaugeWilsonExpectation_mem_Icc incidence K hK _).1
      have hunion_nonneg : 0 <= gaugeWilsonExpectation incidence K
          (gaugeSurfaceBoundary incidence (S.biUnion D)) :=
        (gaugeWilsonExpectation_mem_Icc incidence K hK _).1
      have hmul := gaugeWilsonExpectation_mul_le_symmDiff incidence K
        (fun p => (hK p).le)
        (gaugeSurfaceBoundary incidence (D i))
        (gaugeSurfaceBoundary incidence (S.biUnion D))
      rw [Finset.prod_insert hi, Finset.biUnion_insert]
      calc
        gaugeWilsonExpectation incidence K
              (gaugeSurfaceBoundary incidence (D i)) *
            ∏ j ∈ S, gaugeWilsonExpectation incidence K
              (gaugeSurfaceBoundary incidence (D j)) <=
            gaugeWilsonExpectation incidence K
                (gaugeSurfaceBoundary incidence (D i)) *
              gaugeWilsonExpectation incidence K
                (gaugeSurfaceBoundary incidence (S.biUnion D)) :=
          mul_le_mul_of_nonneg_left (ih hrest) hi_nonneg
        _ <= gaugeWilsonExpectation incidence K
            (gaugeSurfaceBoundary incidence (D i) ∆
              gaugeSurfaceBoundary incidence (S.biUnion D)) := hmul
        _ = gaugeWilsonExpectation incidence K
            (gaugeSurfaceBoundary incidence (D i ∪ S.biUnion D)) := by
          rw [gaugeSurfaceBoundary_union_of_disjoint incidence hsurface]

end
end StatMech.FrontierA
