/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def shb_actualExplorationFiberMass
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)] :
    shb_ExplorationFiberMass V := fun d word =>
  ∑' m : d.graph.edgeFinset -> Nat,
    if sources d.graph (ofEdgeFun d.graph m) = sourceClass d word /\
        selector d word m then
      weight d.graph beta J (ofEdgeFun d.graph m)
    else 0


def shb_ActualExplorationFiberRealizes
    (beta : Real) (J : Sym2 V -> Real)
    (actualMass : shb_ExplorationFiberMass V) : Prop :=
  (forall d, actualMass d [] = currentSum d.graph beta J ∅) /\
  (forall d s ss, s ∈ d.active ->
    actualMass d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        actualMass (shb_BackboneExplorationDomain.advance d s) ss) /\
  (forall d s ss, s ∉ d.active -> actualMass d (s :: ss) = 0)


end
end StatMech.Sharpness
