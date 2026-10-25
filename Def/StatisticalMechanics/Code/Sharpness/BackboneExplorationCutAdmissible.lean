/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationCutAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationRealization.Part12
import Instance.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

def shb_CutPredicateAdmissible
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (full : (G.edgeFinset -> Nat) -> Prop)
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop) : Prop :=
  forall a b,
    full (shb_cutJoin G P (a, b)) <-> left a /\ right b


noncomputable def shb_cutFullPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (full : (G.edgeFinset -> Nat) -> Prop) [DecidablePred full] : Real :=
  tsum fun m => if full m then weight G beta J (ofEdgeFun G m) else 0


noncomputable def shb_cutLeftPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (left : ({e : G.edgeFinset // P e} -> Nat) -> Prop)
    [DecidablePred left] : Real :=
  tsum fun a => if left a then shb_cutLeftWeight G beta J P a else 0


noncomputable def shb_cutRightPredicateMass
    (beta : Real) (J : Sym2 V -> Real)
    (P : G.edgeFinset -> Prop) [DecidablePred P]
    (right : ({e : G.edgeFinset // Not (P e)} -> Nat) -> Prop)
    [DecidablePred right] : Real :=
  tsum fun b => if right b then shb_cutRightWeight G beta J P b else 0

end
end StatMech.Sharpness
