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
import Def.v1.Atlas.TensorCategories.code.TaftConcrete.Part3
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

variable [Fact (q ^ n = 1)]

/-- `Module.finrank k (TaftAlgebraType n q k) = n * n`. -/
lemma finrank_eq : Module.finrank k (TaftAlgebraType n q k) = n * n := by
  rw [LinearEquiv.finrank_eq toFunEquiv, Module.finrank_pi_fintype, Module.finrank_self,
      Finset.sum_const, smul_eq_mul, mul_one, Finset.card_univ, Fintype.card_prod]
  simp [Fintype.card_fin]

end TaftAlgebraType
