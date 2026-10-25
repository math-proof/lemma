/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def shb_LocalSourceSelectorAdmissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (A Aleft Aright : Finset V)
    (selector : (G.edgeFinset -> Nat) -> Prop)
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) : Prop :=
  shb_CutPredicateAdmissible G P
    (fun m => sources G (ofEdgeFun G m) = A /\ selector m)
    (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
      leftSelector a)
    (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
      rightSelector b)


end
end StatMech.Sharpness
