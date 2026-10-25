/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/gc9assembledDnonneg.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Walls.gc8core.Part2
import Theorem.StatisticalMechanics.Code.Walls.gc8crossingallconn
open Finset BigOperators SimpleGraph
open scoped Sym2 symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]

variable {ι : Type*} [DecidableEq ι] [Fintype ι]


theorem gc9_assembled_D_term_nonneg (J : Sym2 V → ℝ) (δ : V → V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ x y, 0 ≤ δ x y) (x y : V) :
    0 ≤ J s(x, y) * δ x y :=
  mul_nonneg (hJ _) (hδ x y)


theorem gc9_assembled_D_nonneg (J : Sym2 V → ℝ) (δ : V → V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ x y, 0 ≤ δ x y) :
    0 ≤ ∑ x : V, ∑ y : V, J s(x, y) * δ x y :=
  Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => gc9_assembled_D_term_nonneg J δ hJ hδ x y


theorem gc9_assembled_D_edges_nonneg (J : Sym2 V → ℝ) (δe : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ e, 0 ≤ δe e) :
    0 ≤ ∑ e : Sym2 V, J e * δe e :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hJ e) (hδ e)


end StatMech.Walls
