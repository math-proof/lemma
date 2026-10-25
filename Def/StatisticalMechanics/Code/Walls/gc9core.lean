/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc9Znormaliserpos
import Theorem.StatisticalMechanics.Code.Walls.gc9assembledDnonneg.Part4
import Theorem.StatisticalMechanics.Code.Walls.gc9deltadef
import Theorem.StatisticalMechanics.Code.Walls.gc9Jnonneg
import Theorem.StatisticalMechanics.Code.Walls.gc9betaderivcov3
import Theorem.StatisticalMechanics.Code.Walls.gc9switching
import Theorem.StatisticalMechanics.Code.Walls.gc9eq15insertion
import Theorem.StatisticalMechanics.Code.Walls.gc6_ghostgraph
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

open StatMech.Sharpness.FieldGhostDict

open StatMech.Sharpness.GhostCurrentRep

open StatMech.Sharpness.FluxEdgeCopy (sourcePairDisconnSum sourcePairDisconnSum_eq_edgecopy)

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


noncomputable def gc9_assembledD_pair (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g x y : V) : ℝ :=
  J s(x, y) * gc9_pivotalMass ends F o g x y


end StatMech.Walls
