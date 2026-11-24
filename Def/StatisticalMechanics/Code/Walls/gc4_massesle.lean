module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.gc3_core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.gc2_shiftbij
public import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
open Finset BigOperators SimpleGraph Set
open scoped symmDiff
open Classical
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc4_massesle.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Sharpness StatMech.Sharpness.RandomCurrent

open StatMech.Ising

open StatMech.Walls.GhcEqGap

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]


def gc4_MassesLe (ends : ι → Sym2 V) (M : Finset (Finset ι)) (A : Finset V)
    (Φ : Finset ι → Finset ι → ℝ) (o x y : V) : Prop :=
  (∑ m ∈ M, aie_mass ends m (Φ m) A)
    ≤ (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {x, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, y}))
      + (∑ m ∈ M, aie_mass ends m (Φ m) (A ∆ {o, x}))


end StatMech.Walls
