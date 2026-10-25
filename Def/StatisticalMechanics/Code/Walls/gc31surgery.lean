/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc31surgery.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc30reroute
import Theorem.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
import Theorem.StatisticalMechanics.Code.Ising.BackboneExists
import Theorem.StatisticalMechanics.Code.Ising.HdomMultiplicity.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Theorem.StatisticalMechanics.Code.Walls.gc31surgery
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


def gc31_MassDoublingSurgery (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Sharpness.Current V))
    (B : Finset V) (o x y : V) : Prop :=
  ∃ Φ : Sharpness.Current V → Sharpness.Current V,
    (∀ m ∈ bbr_allFilter G M o x y, Φ m ∈ bbr_noneFilter G M o x y)
    ∧ (Set.InjOn Φ (bbr_allFilter G M o x y))
    ∧ (∀ m ∈ bbr_allFilter G M o x y, 2 * hnw_mass G β J m B ≤ hnw_mass G β J (Φ m) B)


end StatMech.Walls
