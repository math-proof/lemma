/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable instance shb_cutLocalSourceSelector_decidable
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (Aleft Aright : Finset V)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector] :
    DecidablePred
      (shb_cutLocalSourceSelector G P Aleft Aright leftSelector rightSelector) :=
  Classical.decPred _


end
end StatMech.Sharpness
