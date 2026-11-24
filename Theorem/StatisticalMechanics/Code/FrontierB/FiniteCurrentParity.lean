module
public import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentMeasures
public import Theorem.StatisticalMechanics.Code.Sharpness.HighTempSources.Part3
public import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity
open MeasureTheory
open scoped BigOperators ENNReal


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParity.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem tanh_nonneg_of_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.tanh x := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.2 hx) (Real.cosh_pos x).le

end StatMech.FrontierB
