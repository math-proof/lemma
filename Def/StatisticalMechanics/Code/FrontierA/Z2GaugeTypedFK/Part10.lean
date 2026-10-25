/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFK.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonFreeEnergy.Part3
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.EdwardsSokal.Part7
import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFK.Part7
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech.FrontierA

noncomputable section

variable {P V : Type*} [Fintype P] [DecidableEq P]
  [Fintype V] [DecidableEq V]


noncomputable def typedConstOnOpenEquiv
    (ends : P -> V × V) (omega : P -> Bool) :
    ((typedOpenGraph ends omega).ConnectedComponent -> Bool) ≃
      {sigma : V -> Bool // TypedSignedCompatible ends ∅ omega sigma} where
  toFun tau := ⟨fun v => tau ((typedOpenGraph ends omega).connectedComponentMk v), by
    rw [typedSignedCompatible_empty_iff_graphConstant]
    intro x y hxy
    congr 1
    exact SimpleGraph.ConnectedComponent.connectedComponentMk_eq_of_adj hxy⟩
  invFun sigma := SimpleGraph.ConnectedComponent.lift sigma.1 (by
    intro v w path hpath
    clear hpath
    have hc := (typedSignedCompatible_empty_iff_graphConstant
      ends omega sigma.1).mp sigma.2
    induction path with
    | nil => rfl
    | @cons u v z huv p ih =>
        exact (hc u v huv).trans ih)
  left_inv tau := by
    funext c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | _ v => rfl
  right_inv sigma := by
    apply Subtype.ext
    funext v
    rfl

end
end StatMech.FrontierA
