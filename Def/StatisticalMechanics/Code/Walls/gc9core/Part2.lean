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
import Theorem.StatisticalMechanics.Code.Walls.gc9core
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


noncomputable def gc9_deltaEdge (β h : ℝ) (o : V) (e : Sym2 V) : ℝ :=
  Sym2.lift ⟨fun x y =>
    sourcePairDisconnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
      (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)) ∅ (some o) none,
    by intro a b; simp only []; congr 3; rw [Finset.pair_comm a b]⟩ e

end StatMech.Walls
