module
public import Mathlib
public import Theorem.StatisticalMechanics.Code.Walls.gc_core.Part2
public import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleurselleq
public import Theorem.StatisticalMechanics.Code.Walls.gc5_ensembleprob
public import Theorem.StatisticalMechanics.Code.Walls.gc5_bracketsign
public import Theorem.StatisticalMechanics.Code.Walls.gc5_eqswi
public import Theorem.StatisticalMechanics.Code.Ising.EnsembleGHS
public import Theorem.StatisticalMechanics.Code.Walls.gc5_core
open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 1600000


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc5_core.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

open StatMech.Walls.GhcEqGap

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


def gc5_FamilyRealise (β h : ℝ) (o : V) : Prop :=
  ∀ x y : V, o ≠ x → o ≠ y → x ≠ y →
    ∃ (J : Sym2 V → ℝ) (μ : ℝ) (M : Finset (Ising.Current V)) (B : Finset V) (o' x' y' : V),
      (0 ≤ β) ∧ (∀ e, 0 ≤ J e) ∧ (0 ≤ μ)
      ∧ eg_ursell3 G β h o x y = -2 * μ * tcp_allConnProb G β J M B o' x' y'


end StatMech.Walls
