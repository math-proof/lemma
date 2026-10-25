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
import Def.v1.Atlas.TensorCategories.code.Proposition_1_27_1.Part4
universe u


noncomputable section

namespace EGNO.Prop1271

section Proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

/-- Additive group structure on `ComoduleExt1 g h` transported from the quotient module. -/
noncomputable instance ComoduleExt1.instAddCommGroup {g h : C} :
    AddCommGroup (ComoduleExt1 (k := k) g h) :=
  (ext1EquivSkewQuot (k := k)).addCommGroup

/-- `k`-module structure on `ComoduleExt1 g h` transported from the quotient module. -/
noncomputable instance ComoduleExt1.instModule {g h : C} :
    Module k (ComoduleExt1 (k := k) g h) :=
  Equiv.module k (ext1EquivSkewQuot (k := k))

end Proof
end EGNO.Prop1271
end
