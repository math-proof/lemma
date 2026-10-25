/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Tactic.FinCases
import Mathlib.Algebra.Algebra.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Data.Fintype.Prod
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Def.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

variable [Fact (q ^ n = 1)]

/-- The coefficient of `e ij` at index `p` is `1` iff `ij = p`, else `0`. -/
@[simp] lemma coeff_e (ij p : Fin n × Fin n) :
    (e ij : TaftAlgebraType n q k).coeff p = if ij = p then 1 else 0 := rfl

end TaftAlgebraType
