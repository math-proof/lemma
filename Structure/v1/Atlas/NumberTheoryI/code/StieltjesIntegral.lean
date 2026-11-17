/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Order.Fin.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic


public section

namespace RiemannStieltjes

structure IntervalPartition (a b : ℝ) where
  n : ℕ
  hn : 0 < n
  pts : Fin (n + 1) → ℝ
  first : pts ⟨0, Nat.zero_lt_succ n⟩ = a
  last : pts ⟨n, Nat.lt_succ_iff.mpr le_rfl⟩ = b
  strict_mono : StrictMono pts

end RiemannStieltjes
