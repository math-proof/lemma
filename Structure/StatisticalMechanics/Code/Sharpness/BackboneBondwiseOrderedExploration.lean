/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneBondwiseOrderedExploration.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BackboneExplorationSelector.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCut.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneActualSelectorSwitching.Part3
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration.Part5
open Finset
open scoped symmDiff

set_option linter.unusedSectionVars false


namespace StatMech.Sharpness

namespace BackboneDeterminedCutSwitching

open FluxEdgeCopy

open BackboneLabeledSwitching

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

variable {D : Type*}

structure BondwiseP2Reindex
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) where
  pathCopies : ∀ m : d.graph.edgeFinset -> Nat,
    Finset (FluxEdgeCopy.Copy d.graph m)
  path_sources : ∀ (m : d.graph.edgeFinset -> Nat),
    RandomCurrent.sources (endsM d.graph m) (pathCopies m) = C
  path_supported : ∀ (m : d.graph.edgeFinset -> Nat),
    SupportedInCut d.graph m
      ((X.bondwiseOrdered.tests x).determinedCut accepted) (pathCopies m)
  left_reindex :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawFiberMass d.graph beta J m A
          (BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix bit)
  right_reindex :
    shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss =
      ∑' m : d.graph.edgeFinset -> Nat,
        rawFiberMass d.graph beta J m (A ∆ C)
          (BondwiseSuffixEvent d.graph X (X.advance x accepted) suffix bit)


end BackboneDeterminedCutSwitching
end StatMech.Sharpness
