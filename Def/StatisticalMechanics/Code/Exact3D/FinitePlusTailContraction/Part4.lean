/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/FinitePlusTailContraction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Normed.Lp.lpSpace
import Theorem.StatisticalMechanics.Code.Exact3D.FixedPointSkeleton.Part23
import Theorem.StatisticalMechanics.Code.Exact3D.InfiniteTailSummability.Part5
import Theorem.StatisticalMechanics.Code.Exact3D.FinitePlusTailContraction.Part3
open scoped BigOperators ENNReal NNReal


namespace StatMech

namespace Exact3D

namespace SummableTail

variable {α : Type*}


noncomputable def toLpOne (u : SummableTail α) :
    lp (fun _ : α => ℝ) (1 : ℝ≥0∞) :=
  ⟨u.coeff, by
    change Memℓp u.coeff (1 : ℝ≥0∞)
    rw [memℓp_gen_iff (p := (1 : ℝ≥0∞)) (by norm_num)]
    simpa [Real.norm_eq_abs] using u.summable_abs⟩


noncomputable def ofLpOne
    (f : lp (fun _ : α => ℝ) (1 : ℝ≥0∞)) : SummableTail α where
  coeff := fun a => f a
  summable_abs := by
    have hf := (lp.memℓp f).summable (p := (1 : ℝ≥0∞)) (by norm_num)
    simpa [Real.norm_eq_abs] using hf


noncomputable def equivLpOne :
    SummableTail α ≃ lp (fun _ : α => ℝ) (1 : ℝ≥0∞) where
  toFun := toLpOne
  invFun := ofLpOne
  left_inv := by
    intro u
    ext a
    rfl
  right_inv := by
    intro f
    ext a
    rfl


end SummableTail
end Exact3D
end StatMech
