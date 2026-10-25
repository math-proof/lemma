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
import Def.v1.Atlas.TensorCategories.code.Proposition_1_27_1.Part3
universe u


noncomputable section

namespace EGNO.Prop1271

section Proof

variable {k : Type u} {C : Type u} [Field k] [AddCommGroup C] [Module k C] [Coalgebra k C]

abbrev SkewQuot (g h : C) :=
  (skewPrimitiveSpace (R := k) g h) ⧸
    (Submodule.comap (skewPrimitiveSpace (R := k) g h).subtype
      (trivialSkewPrimitiveSubspace (k := k) g h))

end Proof
end EGNO.Prop1271
end
