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
import Theorem.v1.Atlas.TensorCategories.code.Proposition_1_27_1
universe u


noncomputable section

namespace EGNO.Prop1271

section ComoduleExt

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Setoid structure on comodule extensions of `g` by `h` given by `ComoduleExtension.Equiv`. -/
instance ComoduleExtension.setoid (g h : C) :
    Setoid (ComoduleExtension (k := k) g h) where
  r := ComoduleExtension.Equiv
  iseqv := {
    refl := ComoduleExtension.Equiv.refl
    symm := ComoduleExtension.Equiv.symm
    trans := ComoduleExtension.Equiv.trans
  }

end ComoduleExt
end EGNO.Prop1271
end
