/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc84b_grahamsospositiv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc83crosspairing.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc27polyineq.Part2
open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc84b_ghsResidual (c : Finset (Fin 4) → ℝ) : ℝ :=
  c {0, 3} * c {1, 2} + c {1, 3} * c {0, 2} + c {2, 3} * c {0, 1}
    - c {0, 1, 2, 3} - 2 * (c {0, 3} * c {1, 3} * c {2, 3})


def gc84b_GriffithsFamily (c : Finset (Fin 4) → ℝ) : Prop :=
  c ∅ = 1 ∧ (∀ S : Finset (Fin 4), 0 ≤ c S) ∧ (∀ A B : Finset (Fin 4), c A * c B ≤ c (A ∆ B))


noncomputable def gc84b_parityCorr (S : Finset (Fin 4)) : ℝ :=
  if S = ∅ ∨ S = Finset.univ then 1 else 0


end StatMech.Walls
