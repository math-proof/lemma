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
import Structure.StatisticalMechanics.Code.Sharpness.BackboneBondwiseOrderedExploration
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

theorem BondwiseP2Reindex.path_source_eq_empty
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) :
    C = ∅ := by
  let m0 : d.graph.edgeFinset -> Nat := fun _ => 0
  have hcopies : R.pathCopies m0 = ∅ := by
    ext i
    exact Fin.elim0 i.2
  calc
    C = RandomCurrent.sources (endsM d.graph m0) (R.pathCopies m0) :=
      (R.path_sources m0).symm
    _ = RandomCurrent.sources (endsM d.graph m0) ∅ := by rw [hcopies]
    _ = ∅ := by
      ext v
      simp [RandomCurrent.mem_sources, RandomCurrent.degK]


theorem bondwiseP2Reindex_isEmpty_of_path_source_ne_empty
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V)) (hC : C ≠ ∅) :
    IsEmpty
      (BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) := by
  constructor
  intro R
  exact hC R.path_source_eq_empty


theorem actualMass_active_of_bondwiseSuffixToggle
    (X : shb_DynamicEdgeExploration D (Sym2 V)) (x : D)
    (accepted : Sym2 V) (suffix : List (Sym2 V))
    (hfresh : SuffixFresh X x accepted suffix)
    (bit : Nat -> Bool) (A C : Finset V)
    (S : shb_CurrentDynamicSelector (V := V))
    (beta : Real) (J : Sym2 V -> Real)
    (d : shb_ExplorationDomain V) (s : shb_ExplorationSegment V)
    (ss : List (shb_ExplorationSegment V))
    (R : BondwiseP2Reindex X x accepted suffix bit A C S beta J d s ss) :
    S.actualMass beta J d (s :: ss) *
        currentSum (shb_BackboneExplorationDomain.advance d s).graph
          beta J ∅ =
      shb_segmentNum beta J d s *
        S.actualMass beta J
          (shb_BackboneExplorationDomain.advance d s) ss := by
  rw [R.left_reindex, R.right_reindex]
  apply tsum_congr
  intro m
  exact rawFiberMass_eq_of_bondwiseSuffixToggle d.graph X x accepted
    suffix hfresh bit beta J m A C (R.pathCopies m)
    (R.path_sources m) (R.path_supported m)

end BackboneDeterminedCutSwitching
end StatMech.Sharpness
