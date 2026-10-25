/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc33witness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc32surgery
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.TwoReplica.Part3
import Abbrev.StatisticalMechanics.Code.Walls.gc33witness
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


variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc33_ma : Sharpness.Current (Fin 5) :=
  fun e => if e = s(0,1) ∨ e = s(1,2) ∨ e = s(0,2) then 1 else 0


def gc33_mstar : Sharpness.Current (Fin 5) := fun e => if e = s(3,4) then 2 else 0


noncomputable def gc33_J : Sym2 (Fin 5) → ℝ := fun e => if e = s(3,4) then 8 else 1


noncomputable def gc33_M : Finset (Sharpness.Current (Fin 5)) := {gc33_ma, gc33_mstar}

end StatMech.Walls
