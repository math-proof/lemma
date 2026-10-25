/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc6_core.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc5_core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc6_munonneg
import Theorem.StatisticalMechanics.Code.Walls.gc6_core
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc6_EqSwiIdentity (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    ∃ (J : Sym2 V → ℝ) (μ : ℝ) (M : Finset (Ising.Current V)) (B : Finset V) (o' x' y' : V),
      (0 ≤ β) ∧ (∀ e, 0 ≤ J e) ∧ (0 ≤ μ)
      ∧ (o' ≠ x') ∧ (o' ≠ y') ∧ (x' ≠ y')
      ∧ (0 < tcp_partitionFunction G β J M B)
      ∧ eg_ursell3 G β h o x y * tcp_partitionFunction G β J M B
          = μ * egh_ensembleUrsell G β J M B o' x' y'


end StatMech.Walls
