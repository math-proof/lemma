/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectHorizontalCylinderLaw.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCutPushforward.Part2
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectCutFreeLaw.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKRectHorizontalCylinderLaw.Part5
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.FrontierD

noncomputable section

open StatMech


theorem fkRectHorizontalCylinder_ecz_eventWeight_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (A : Set R.Configuration) :
    FK.ecz_eventWeight (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q
        (fkRectHorizontalCylinderEdgeEvent R A) =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectHorizontalCutClosedReducedEventWeight R q A := by
  unfold FK.ecz_eventWeight
    fkRectHorizontalCutClosedReducedEventWeight
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (fkRectHorizontalCutClosedEdgeConfigEquiv R)
  intro omega
  by_cases hA : omega.1 ∈ A
  · rw [Set.indicator_of_mem hA,
      Set.indicator_of_mem (show
        fkRectHorizontalCutClosedEdgeConfigEquiv R omega ∈
          fkRectHorizontalCylinderEdgeEvent R A by
            simpa [fkRectHorizontalCylinderEdgeEvent])]
    rw [fkRectHorizontalCylinder_fkWeight_critical_eq R hq]
  · rw [Set.indicator_of_notMem hA,
      Set.indicator_of_notMem (show
        fkRectHorizontalCutClosedEdgeConfigEquiv R omega ∉
          fkRectHorizontalCylinderEdgeEvent R A by
            simpa [fkRectHorizontalCylinderEdgeEvent])]
    simp

theorem fkRectHorizontalCylinder_ecz_fkZEdge_eq
    (R : FKRectTorus) {q : Real} (hq : 0 < q) :
    FK.ecz_fkZEdge (fkRectHorizontalCylinderGraph R)
        (fkRectCriticalP q) q =
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card *
        fkRectHorizontalCutClosedReducedZ R q := by
  rw [← fkRectHorizontalCutClosedReducedEventWeight_univ]
  simpa [fkRectHorizontalCylinderEdgeEvent, FK.ecz_eventWeight,
    FK.ecz_fkZEdge] using
      fkRectHorizontalCylinder_ecz_eventWeight_eq
        R hq (Set.univ : Set R.Configuration)


theorem fkRectCriticalHorizontalCutEventMass_eq_cylinderGraph
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (A : Set R.Configuration) :
    fkRectCriticalHorizontalCutEventMass R q A =
      ∑ sigma : ConfigSpace (Sym2 R.Vertex),
        (FK.ecz_closeOff (fkRectHorizontalCylinderGraph R) ⁻¹'
          fkRectHorizontalCylinderEdgeEvent R A).indicator
            (fun _ => (1 : Real)) sigma *
          FK.fkProb (fkRectHorizontalCylinderGraph R)
            (fkRectCriticalP q) q sigma := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  rw [fkRectCriticalHorizontalCutEventMass_eq_reduced R hq A,
    FK.ecz_eventProb_eq]
  rw [fkRectHorizontalCylinder_ecz_eventWeight_eq R hq0,
    fkRectHorizontalCylinder_ecz_fkZEdge_eq R hq0]
  have hp1 : 0 < 1 - fkRectCriticalP q := by
    linarith [fkRectCriticalP_lt_one hq0]
  have hfactor :
      (1 - fkRectCriticalP q) ^
          (fkRectHorizontalCylinderGraph R).edgeFinset.card ≠ 0 :=
    (pow_pos hp1 _).ne'
  field_simp

end
end StatMech.FrontierD
