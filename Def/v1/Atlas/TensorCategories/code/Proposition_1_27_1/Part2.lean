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
import Structure.v1.Atlas.TensorCategories.code.Proposition_1_27_1
universe u


noncomputable section

namespace EGNO.Prop1271

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Two comodule extensions are equivalent if their underlying skew-primitive elements
differ by a multiple of `h - g`. -/
def ComoduleExtension.Equiv {g h : C} (E₁ E₂ : ComoduleExtension (k := k) g h) : Prop :=
  E₁.x - E₂.x ∈ trivialSkewPrimitiveSubspace (k := k) g h

end ComoduleExt
end EGNO.Prop1271
end
