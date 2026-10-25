/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeWilsonAffine.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeIsingAdapter
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part2
open scoped symmDiff
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

variable {E P V : Type*} [Fintype E] [DecidableEq E]
  [Fintype P] [DecidableEq P] [Fintype V] [DecidableEq V]

noncomputable def cutSpaceShiftEquiv
    (G : SimpleGraph V) [DecidableRel G.Adj] (D : Finset (Sym2 V)) :
    {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G} ≃
      {gamma : Finset (Sym2 V) //
        gamma ∈ shiftedDualCutFamily (G := G) D} where
  toFun delta := ⟨delta.1 ∆ D, by
    unfold shiftedDualCutFamily
    rw [Finset.mem_image]
    exact ⟨delta.1, delta.2, rfl⟩⟩
  invFun gamma := ⟨gamma.1 ∆ D, by
    have hmem := gamma.2
    unfold shiftedDualCutFamily at hmem
    rw [Finset.mem_image] at hmem
    obtain ⟨delta, hdelta, hgamma⟩ := hmem
    have hcancel : gamma.1 ∆ D = delta := by
      rw [← hgamma]
      simp
    simpa only [hcancel] using hdelta⟩
  left_inv delta := by
    apply Subtype.ext
    simp
  right_inv gamma := by
    apply Subtype.ext
    simp


noncomputable def gaugeWilsonShiftedCutEquiv
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (incidence : P → Finset E) (L : Finset E)
    (dualEdge : P ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset P // A ∈ gaugeClosedSurfaceFamily incidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (D : Finset P) (hD : HasWilsonBoundary incidence D L) :
    {A : Finset P // A ∈ gaugeWilsonSurfaceFamily incidence L} ≃
      {gamma : Finset (Sym2 V) // gamma ∈ shiftedDualCutFamily
        (G := G) (D.map (dualPlaquetteEmbedding dualEdge))} :=
  (gaugeWilsonClosedEquiv incidence L D hD).trans
    (closedEquiv.trans
      (cutSpaceShiftEquiv G (D.map (dualPlaquetteEmbedding dualEdge))))


end StatMech.FrontierA
