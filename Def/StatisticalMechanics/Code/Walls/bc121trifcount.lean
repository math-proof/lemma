/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc121trifcount.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc112sepcontract.Part7
import Theorem.StatisticalMechanics.Code.Walls.bc118pathmember
open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


noncomputable def bc121_badLeaves {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : V → Prop) [DecidablePred B] : Finset V :=
  univ.filter (fun v => G.degree v = 1 ∧ ¬ B v)


def bc121_BAnchored {V : Type*} [Fintype V] (F : SimpleGraph V) [DecidableRel F.Adj]
    (B : V → Prop) : Prop :=
  F.IsAcyclic ∧ (∀ v, F.degree v = 1 → B v)


end StatMech.Walls
