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
public import Structure.v1.Atlas.NumberTheoryI.code.StieltjesIntegral

@[expose] public section

namespace RiemannStieltjes

variable {a b : ℝ}

def IntervalPartition.IsRefinementOf (P Q : IntervalPartition a b) : Prop :=
  ∀ j : Fin (Q.n + 1), ∃ i : Fin (P.n + 1), P.pts i = Q.pts j

end RiemannStieltjes
