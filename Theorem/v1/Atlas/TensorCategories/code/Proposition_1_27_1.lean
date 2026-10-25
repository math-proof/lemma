/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_27_1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Def.v1.Atlas.TensorCategories.code.Proposition_1_27_1.Part2
universe u


noncomputable section

namespace EGNO.Prop1271

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Equivalence of comodule extensions is reflexive. -/
theorem ComoduleExtension.Equiv.refl {g h : C} (E : ComoduleExtension (k := k) g h) :
    ComoduleExtension.Equiv E E := by
  unfold ComoduleExtension.Equiv
  simp [trivialSkewPrimitiveSubspace]

/-- Equivalence of comodule extensions is symmetric. -/
theorem ComoduleExtension.Equiv.symm {g h : C}
    {E₁ E₂ : ComoduleExtension (k := k) g h} (h_eq : ComoduleExtension.Equiv E₁ E₂) :
    ComoduleExtension.Equiv E₂ E₁ := by
  unfold ComoduleExtension.Equiv at *
  rwa [show E₂.x - E₁.x = -(E₁.x - E₂.x) from (neg_sub E₁.x E₂.x).symm, neg_mem_iff]

/-- Equivalence of comodule extensions is transitive. -/
theorem ComoduleExtension.Equiv.trans {g h : C}
    {E₁ E₂ E₃ : ComoduleExtension (k := k) g h}
    (h₁₂ : ComoduleExtension.Equiv E₁ E₂) (h₂₃ : ComoduleExtension.Equiv E₂ E₃) :
    ComoduleExtension.Equiv E₁ E₃ := by
  unfold ComoduleExtension.Equiv at *
  have : E₁.x - E₃.x = (E₁.x - E₂.x) + (E₂.x - E₃.x) := by abel
  rw [this]
  exact Submodule.add_mem _ h₁₂ h₂₃

end ComoduleExt
end EGNO.Prop1271
end
