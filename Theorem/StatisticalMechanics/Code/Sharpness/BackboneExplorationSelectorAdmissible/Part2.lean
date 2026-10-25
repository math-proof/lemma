/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneExplorationSelectorAdmissible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationCutAdmissible.Part3
import Def.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelectorAdmissible.Part2
open SimpleGraph Finset
open scoped BigOperators symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem shb_actualExplorationFiberMass_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector)) :
    shb_actualExplorationFiberMass beta J sourceClass selector =
      shb_generatedExplorationFiberMass beta J := by
  apply shb_LocalSelectorFiberCutResummation_unique beta J
  exact hrealizes


theorem shb_actualExplorationFiberRealizes_iff_eq_generated
    (beta : Real) (J : Sym2 V -> Real)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)] :
    shb_ActualExplorationFiberRealizes beta J
        (shb_actualExplorationFiberMass beta J sourceClass selector) <->
      shb_actualExplorationFiberMass beta J sourceClass selector =
        shb_generatedExplorationFiberMass beta J := by
  exact shb_LocalSelectorFiberCutResummation_iff_eq_generated beta J
    (shb_actualExplorationFiberMass beta J sourceClass selector)


theorem shb_actualExploration_rho_eq_weight
    (beta : Real) (J : Sym2 V -> Real)
    (hbeta : 0 <= beta) (hJ : forall e, 0 <= J e)
    (hdom : shb_BackboneExplorationDomain.LocalDomainResummation beta J)
    (sourceClass : shb_ExplorationDomain V ->
      List (shb_ExplorationSegment V) -> Finset V)
    (selector : (d : shb_ExplorationDomain V) ->
      List (shb_ExplorationSegment V) ->
      (d.graph.edgeFinset -> Nat) -> Prop)
    [∀ d word, DecidablePred (selector d word)]
    (hrealizes : shb_ActualExplorationFiberRealizes beta J
      (shb_actualExplorationFiberMass beta J sourceClass selector))
    (d : shb_ExplorationDomain V) (word : List (shb_ExplorationSegment V)) :
    shb_normalizedExplorationRho beta J
        (shb_actualExplorationFiberMass beta J sourceClass selector) d word =
      (shb_BackboneExplorationDomain.kernel beta J hbeta hJ hdom).weight
        d word := by
  exact shb_randomCurrent_rho_eq_weight beta J hbeta hJ hdom
    (shb_actualExplorationFiberMass beta J sourceClass selector)
    hrealizes d word


end
end StatMech.Sharpness
