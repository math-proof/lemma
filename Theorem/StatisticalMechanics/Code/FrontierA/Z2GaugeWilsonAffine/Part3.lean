/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part2
open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

theorem gaugeWilsonShiftedCutEquiv_apply
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (L : Finset E)
    (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
    (D : Finset P) (hD : HasWilsonBoundary incidence D L)
    (A : {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L}) :
    (gaugeWilsonShiftedCutEquiv incidence L dualEdge closedEquiv D hD A).1 =
      A.1.map (dualPlaquetteEmbedding dualEdge) := by
  change (closedEquiv
      ((gaugeWilsonClosedEquiv incidence L D hD) A)).1 ∆
        D.map (dualPlaquetteEmbedding dualEdge) =
    A.1.map (dualPlaquetteEmbedding dualEdge)
  rw [hclosed]
  change (A.1 ∆ D).map (dualPlaquetteEmbedding dualEdge) ∆
      D.map (dualPlaquetteEmbedding dualEdge) =
    A.1.map (dualPlaquetteEmbedding dualEdge)
  rw [map_symmDiff_embedding]
  simp


theorem gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (K : P → ℝ) (hK : ∀ p, 0 < K p)
    (L : Finset E) (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge))
    (D : Finset P) (hD : HasWilsonBoundary incidence D L) :
    gaugeWilsonExpectation incidence K L =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          (D.map (dualPlaquetteEmbedding dualEdge)),
          ∏ e ∈ gamma, Real.exp (-2 * dualIsingCoupling dualEdge K e)) /
        (∑ delta ∈ StatMech.Ising.cutSpace G,
          ∏ e ∈ delta, Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
  exact gaugeWilsonExpectation_eq_dualDisorderRatio incidence K hK L
    (D.map (dualPlaquetteEmbedding dualEdge)) dualEdge closedEquiv hclosed
    (gaugeWilsonShiftedCutEquiv incidence L dualEdge closedEquiv D hD)
    (gaugeWilsonShiftedCutEquiv_apply incidence L dualEdge closedEquiv hclosed D hD)

end StatMech.FrontierA
