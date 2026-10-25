/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/Ergodicity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Def.StatisticalMechanics.Code.Foundations.Ergodicity
open MeasureTheory


namespace StatMech

namespace ConfigSpace

variable {E : Type*} {G : Type*}

section Group

variable [Group G] [MulAction G E]


@[simp] lemma shift_apply (g : G) (ω : ConfigSpace E) (e : E) :
    shift g ω e = ω (g⁻¹ • e) := rfl


@[simp] lemma shift_one : (shift (1 : G) : ConfigSpace E → ConfigSpace E) = id := by
  funext ω e
  simp [shift]


lemma shift_mul (g h : G) :
    (shift (g * h) : ConfigSpace E → ConfigSpace E) = shift g ∘ shift h := by
  funext ω e
  simp [shift, mul_smul]


theorem measurable_shift (g : G) : Measurable (shift g : ConfigSpace E → ConfigSpace E) :=
  measurable_pi_lambda _ fun e => measurable_pi_apply (g⁻¹ • e)


theorem continuous_shift (g : G) : Continuous (shift g : ConfigSpace E → ConfigSpace E) :=
  continuous_pi fun e => continuous_apply (g⁻¹ • e)


@[simp] lemma shift_inv_comp (g : G) :
    (shift g⁻¹ : ConfigSpace E → ConfigSpace E) ∘ shift g = id := by
  rw [← shift_mul]; simp


@[simp] lemma shift_comp_inv (g : G) :
    (shift g : ConfigSpace E → ConfigSpace E) ∘ shift g⁻¹ = id := by
  rw [← shift_mul]; simp


end Group
end ConfigSpace
end StatMech
