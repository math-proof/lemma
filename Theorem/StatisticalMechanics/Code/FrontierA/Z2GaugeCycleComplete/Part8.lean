/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part7
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem cycleCompleteSurfaceEquiv_apply [Nonempty V]
    (hG : G.Preconnected)
    (A : {A : Finset G.edgeFinset //
      A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG)}) :
    (cycleCompleteSurfaceEquiv G hG A).1 = cycleCompleteEdgeSet G A.1 :=
  rfl

theorem cycleCompleteEdgeSet_eq_dualPlaquetteMap
    (A : Finset G.edgeFinset) :
    cycleCompleteEdgeSet G A =
      A.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset)) := by
  rfl


theorem cycleComplete_gaugePartition_isingDuality [Nonempty V]
    (hG : G.Preconnected) (K : G.edgeFinset → ℝ)
    (hK : ∀ p, 0 < K p) :
    (Real.exp (∑ e ∈ G.edgeFinset,
          dualIsingCoupling (Equiv.refl G.edgeFinset) K e) * 2) *
        gaugePartition (cycleCompleteIncidence G hG) K =
      ((2 : ℝ) ^ Fintype.card (CycleCompleteConstraint G) *
          ∏ p : G.edgeFinset, Real.cosh (K p)) *
        ZJ G.edgeFinset
          (dualIsingCoupling (Equiv.refl G.edgeFinset) K) (fun _ => 0) := by
  apply gaugePartition_isingDuality hG
    (cycleCompleteIncidence G hG) K hK
    (Equiv.refl G.edgeFinset) (cycleCompleteSurfaceEquiv G hG)
  intro A
  exact cycleCompleteEdgeSet_eq_dualPlaquetteMap G A.1


theorem cycleComplete_gaugeWilsonExpectation_eq_dualDisorderRatio [Nonempty V]
    (hG : G.Preconnected) (K : G.edgeFinset → ℝ)
    (hK : ∀ p, 0 < K p)
    (L : Finset (CycleCompleteConstraint G))
    (D : Finset G.edgeFinset)
    (hD : HasWilsonBoundary (cycleCompleteIncidence G hG) D L) :
    gaugeWilsonExpectation (cycleCompleteIncidence G hG) K L =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          (D.map (dualPlaquetteEmbedding (Equiv.refl G.edgeFinset))),
          ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling
            (Equiv.refl G.edgeFinset) K e)) /
        (∑ delta ∈ cutSpace G,
          ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling
            (Equiv.refl G.edgeFinset) K e)) := by
  apply gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    (cycleCompleteIncidence G hG) K hK L (Equiv.refl G.edgeFinset)
    (cycleCompleteSurfaceEquiv G hG)
    (fun A => cycleCompleteEdgeSet_eq_dualPlaquetteMap G A.1) D hD

end
end StatMech.FrontierA
