/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shb_localSourceSelectorMass_factor
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (A Aleft Aright : Finset V)
    (selector : (G.edgeFinset -> Nat) -> Prop) [DecidablePred selector]
    (leftSelector : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred leftSelector]
    (rightSelector : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred rightSelector]
    (hadm : shb_LocalSourceSelectorAdmissible G P A Aleft Aright
      selector leftSelector rightSelector) :
    shb_cutFullPredicateMass G beta J
        (fun m => sources G (ofEdgeFun G m) = A /\ selector m) =
      shb_cutLeftPredicateMass G beta J P
          (fun a => sources G (ofEdgeFun G (shb_cutLeft G P a)) = Aleft /\
            leftSelector a) *
        shb_cutRightPredicateMass G beta J P
          (fun b => sources G (ofEdgeFun G (shb_cutRight G P b)) = Aright /\
            rightSelector b) := by
  exact shb_cutPredicateMass_factor G beta J P _ _ _ hadm


end
end StatMech.Sharpness
