/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc113boundaryforest.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.bc113boundaryforest.Part3
open Set SimpleGraph Finset

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option maxRecDepth 4000


namespace StatMech.Walls

variable {V : Type*} [Fintype V] [DecidableEq V]


open Classical in


noncomputable def bc113_bForest (G : SimpleGraph V) (B : V → Prop) (hreach : bc113_ReachesB G B) :
    SimpleGraph V := by
  classical
  exact SimpleGraph.fromEdgeSet
    {e : Sym2 V | ∃ v : V, ¬ B v ∧ e = s(v, bc113_parent G B hreach v)}


end StatMech.Walls
