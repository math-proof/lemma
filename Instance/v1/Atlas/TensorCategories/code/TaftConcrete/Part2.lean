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
import Def.v1.Atlas.TensorCategories.code.TaftConcrete
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- Multiplication on the Taft algebra: convolution against the basis structure constants. -/
noncomputable instance : Mul (TaftAlgebraType n q k) where
  mul a b := ⟨fun m => ∑ ij : Fin n × Fin n, ∑ cd : Fin n × Fin n,
    a.coeff ij * b.coeff cd * basisMul q ij cd m⟩

end TaftAlgebraType
