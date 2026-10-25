/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectCutFreeLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutSquareEmbedding.Part6
import Theorem.StatisticalMechanics.Code.FK.EdgeConfigEventLaw.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3
import Def.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part3
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectCut_ecz_eventWeight_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    FK.ecz_eventWeight (fkRectCutGraph R) (fkRectCriticalP q) q
        (fkRectCutEdgeEvent R A) =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCutClosedReducedEventWeight R q A := by
  unfold FK.ecz_eventWeight fkRectCutClosedReducedEventWeight
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (fkRectCutClosedEdgeConfigEquiv R)
  intro omega
  by_cases hA : omega.1 ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show fkRectCutClosedEdgeConfigEquiv R omega ∈
        fkRectCutEdgeEvent R A by simpa [fkRectCutEdgeEvent])]
    rw [fkRectCut_fkWeight_critical_eq R hq]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show fkRectCutClosedEdgeConfigEquiv R omega ∉
        fkRectCutEdgeEvent R A by simpa [fkRectCutEdgeEvent])]
    simp

theorem fkRectCut_ecz_fkZEdge_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    FK.ecz_fkZEdge (fkRectCutGraph R) (fkRectCriticalP q) q =
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card *
        fkRectCutClosedReducedZ R q := by
  rw [← fkRectCutClosedReducedEventWeight_univ]
  simpa [fkRectCutEdgeEvent, FK.ecz_eventWeight, FK.ecz_fkZEdge] using
    fkRectCut_ecz_eventWeight_eq R hq (Set.univ : Set R.Configuration)


theorem fkRectCriticalCutFreeEventMass_eq_cutGraph
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (A : Set R.Configuration) :
    fkRectCriticalCutFreeEventMass R q A =
      ∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ecz_closeOff (fkRectCutGraph R) ⁻¹'
          fkRectCutEdgeEvent R A).indicator (fun _ => (1 : Real)) sigma *
          FK.fkProb (fkRectCutGraph R) (fkRectCriticalP q) q sigma := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [fkRectCriticalCutFreeEventMass_eq_reduced R hq A,
    FK.ecz_eventProb_eq]
  rw [fkRectCut_ecz_eventWeight_eq R hq0,
    fkRectCut_ecz_fkZEdge_eq R hq0]
  have hp1 : 0 < 1 - fkRectCriticalP q := by
    linarith [fkRectCriticalP_lt_one hq0]
  have hfactor :
      (1 - fkRectCriticalP q) ^ (fkRectCutGraph R).edgeFinset.card ≠ 0 :=
    (pow_pos hp1 _).ne'
  field_simp

end
end StatMech.FrontierD
