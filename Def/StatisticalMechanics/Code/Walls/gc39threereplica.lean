/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc39threereplica.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc38sharp.Part3
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

open StatMech.Walls.Gc5EqGap StatMech.Walls.GhcEqGap

open StatMech.Sharpness.FluxEdgeCopy

open StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Sharpness (currentSum)


noncomputable def gc39_allConnSum (β h : ℝ) (o x y : V) : ℝ :=
  gc38_sourcePairAllConnSum (withGhost G) β (ghostCoupling h β (fun _ => 1))
    ({some o, some x, some y, none} : Finset (Option V)) (some o) (some x) (some y) none


noncomputable def gc39_csTriple (β h : ℝ) (o x y : V) : ℝ :=
  currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some o, none} : Finset (Option V))
    * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some x, none} : Finset (Option V))
    * currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ({some y, none} : Finset (Option V))


end StatMech.Walls
