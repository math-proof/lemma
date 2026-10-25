/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCubicalWilson.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCubicalWilson.Part3
open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

noncomputable section

theorem cubicalXYSheet_hasWilsonBoundary {a b c : Nat}
    (k : Fin (c + 1)) :
    HasWilsonBoundary (cubicalPlaquetteIncidence (a := a) (b := b) (c := c))
      (cubicalXYSheet k) (cubicalXYLoop k) :=
  hasWilsonBoundary_gaugeSurfaceBoundary _ _


theorem cubicalXYWilsonExpectation_eq_dualDisorderRatio
    {a b c : Nat} {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (k : Fin (c + 1)) (K : CubicalPlaquette a b c → Real)
    (hK : ∀ p, 0 < K p)
    (dualEdge : CubicalPlaquette a b c ≃ G.edgeFinset)
    (closedEquiv :
      {A : Finset (CubicalPlaquette a b c) //
          A ∈ gaugeClosedSurfaceFamily cubicalPlaquetteIncidence} ≃
        {delta : Finset (Sym2 V) // delta ∈ StatMech.Ising.cutSpace G})
    (hclosed : ∀ A,
      (closedEquiv A).1 = A.1.map (dualPlaquetteEmbedding dualEdge)) :
    gaugeWilsonExpectation cubicalPlaquetteIncidence K (cubicalXYLoop k) =
      (∑ gamma ∈ shiftedDualCutFamily (G := G)
          ((cubicalXYSheet k).map (dualPlaquetteEmbedding dualEdge)),
          ∏ e ∈ gamma,
            Real.exp (-2 * dualIsingCoupling dualEdge K e)) /
        (∑ delta ∈ StatMech.Ising.cutSpace G,
          ∏ e ∈ delta,
            Real.exp (-2 * dualIsingCoupling dualEdge K e)) := by
  apply gaugeWilsonExpectation_eq_dualDisorderRatio_of_sheet
    cubicalPlaquetteIncidence K hK (cubicalXYLoop k) dualEdge
    closedEquiv hclosed (cubicalXYSheet k)
  exact cubicalXYSheet_hasWilsonBoundary k

end
end StatMech.FrontierA
