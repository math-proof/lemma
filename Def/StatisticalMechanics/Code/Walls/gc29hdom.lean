/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc29hdom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc28ghsrigid
import Theorem.StatisticalMechanics.Code.Ising.TwoCurrentProbBound
import Theorem.StatisticalMechanics.Code.Ising.CrossClassHdom
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc15core.Part5
import Theorem.StatisticalMechanics.Code.Walls.gc29hdom
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

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc29_BackboneReroute (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (B : Finset V) (o x y : V) : Prop :=
  ∃ R : Sharpness.Current V → ℝ,
    (∀ m, 0 ≤ R m)
    ∧ 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m B)
        ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), R m
    ∧ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), R m
        ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m B


end StatMech.Walls
