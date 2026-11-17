/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsoradialDualSubgraphSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Lean.Elab.Tactic.Omega
public import Def.StatisticalMechanics.Code.FrontierA.IsoradialDualSubgraphSum

public section

namespace StatMech.FrontierA

open Finset

open scoped BigOperators

variable {E K : Type*} [Fintype E] [DecidableEq E]


theorem isoradialCriticalMu_dual (theta : Real) :
    isoradialCriticalMu (Real.pi / 2 - theta) =
      -(isoradialCriticalMu theta)⁻¹ := by
  rw [isoradialCriticalMu, isoradialCriticalMu,
    Real.tan_pi_div_two_sub]
  push_cast
  rw [mul_inv_rev, Complex.inv_I]
  simp only [mul_neg, neg_neg]
  ac_rfl


theorem isoradialCriticalMu_ne_zero {theta : Real}
    (htheta : 0 < theta) (htheta' : theta < Real.pi / 2) :
    isoradialCriticalMu theta ≠ 0 := by
  rw [isoradialCriticalMu, mul_ne_zero_iff]
  exact ⟨Complex.I_ne_zero,
    Complex.ofReal_ne_zero.mpr
      (Real.tan_pos_of_pos_of_lt_pi_div_two htheta htheta').ne'⟩


end StatMech.FrontierA
