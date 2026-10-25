/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def shb_cutLocalSourceSelector
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    (m : G.edgeFinset -> Nat) : Prop := by
  classical
  let ab := shb_cutEquiv G P m
  exact
    (sources G (ofEdgeFun G (shb_cutLeft G P ab.1)) = Aleft /\
      leftSelector ab.1) /\
    (sources G (ofEdgeFun G (shb_cutRight G P ab.2)) = Aright /\
      rightSelector ab.2)

end
end StatMech.Sharpness
