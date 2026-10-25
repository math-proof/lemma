/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionFreeSpinLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits.Part7
import Theorem.StatisticalMechanics.Code.FrontierB.InhomogeneousFiniteVolumeRelabel.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UniqueInfiniteComponent.Part3
open Filter Topology Set
open scoped BigOperators
open Finset


namespace StatMech.FrontierB

open StatMech.Ising StatMech.Sharpness StatMech.Lattice


def interactionBoxVertexIncl (d : Nat) {n m : Nat} (hnm : n ≤ m) :
    interactionBoxVertices d n ↪ interactionBoxVertices d m where
  toFun x := ⟨x.1, mem_interactionBoxVertices.mpr
    (box_mono d hnm (mem_interactionBoxVertices.mp x.2))⟩
  inj' _ _ h := by
    apply Subtype.ext
    exact congrArg (fun y : interactionBoxVertices d m => y.1) h


def interactionBoxPredEquiv (d : Nat) {n m : Nat} (hnm : n ≤ m) :
    interactionBoxVertices d n ≃
      {x : interactionBoxVertices d m // x.1 ∈ box d n} where
  toFun x :=
    ⟨⟨x.1, mem_interactionBoxVertices.mpr
      (box_mono d hnm (mem_interactionBoxVertices.mp x.2))⟩,
      mem_interactionBoxVertices.mp x.2⟩
  invFun x := ⟨x.1.1, mem_interactionBoxVertices.mpr x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end StatMech.FrontierB
