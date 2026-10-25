/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/ActiveInfluenceQOne.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.BeffaraDC.ActiveInfluence.Part2
import Theorem.StatisticalMechanics.Code.BeffaraDC.MaxInfluencePBiased.Part2
import Theorem.StatisticalMechanics.Code.OSSS.CovLowerBound
open scoped BigOperators
open Finset Set


namespace StatMech.BeffaraDC

open StatMech.FK

open StatMech.OSSS

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def edgeFinsetEquivEdgeSet : G.edgeFinset ≃ G.edgeSet where
  toFun e := ⟨e.1, by
    rw [← SimpleGraph.mem_edgeFinset]
    exact e.2⟩
  invFun e := ⟨e.1, by
    rw [SimpleGraph.mem_edgeFinset]
    exact e.2⟩
  left_inv e := by ext; rfl
  right_inv e := by ext; rfl


end StatMech.BeffaraDC
