/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/StieltjesIntegral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Order.Fin.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Structure.v1.Atlas.NumberTheoryI.code.StieltjesIntegral


namespace RiemannStieltjes

variable {a b : ℝ}

def IntervalPartition.IsRefinementOf (P Q : IntervalPartition a b) : Prop :=
  ∀ j : Fin (Q.n + 1), ∃ i : Fin (P.n + 1), P.pts i = Q.pts j

end RiemannStieltjes
