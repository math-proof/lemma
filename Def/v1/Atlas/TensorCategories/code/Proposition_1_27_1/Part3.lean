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
import Instance.v1.Atlas.TensorCategories.code.Proposition_1_27_1
universe u


noncomputable section

namespace EGNO.Prop1271

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- The space of comodule extensions `Ext¹(g, h)` realized as equivalence classes of
skew-primitive elements. -/
def ComoduleExt1 (g h : C) : Type u :=
  Quotient (ComoduleExtension.setoid (k := k) g h)

end ComoduleExt
end EGNO.Prop1271
end
