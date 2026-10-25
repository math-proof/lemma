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
import Instance.v1.Atlas.TensorCategories.code.TaftConcrete
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- Coefficient of the zero element. -/
@[simp] lemma coeff_zero' (i : Fin n × Fin n) : (0 : TaftAlgebraType n q k).coeff i = 0 := rfl

/-- Coefficients distribute over addition. -/
@[simp] lemma coeff_add (a b : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (a + b).coeff i = a.coeff i + b.coeff i := rfl

/-- Coefficients commute with negation. -/
@[simp] lemma coeff_neg (a : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (-a).coeff i = -a.coeff i := rfl

/-- Coefficients distribute over subtraction. -/
@[simp] lemma coeff_sub (a b : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (a - b).coeff i = a.coeff i - b.coeff i := rfl

/-- Coefficients of a scalar multiple are scaled coefficients. -/
@[simp] lemma coeff_smul (r : k) (a : TaftAlgebraType n q k) (i : Fin n × Fin n) :
    (r • a).coeff i = r * a.coeff i := rfl

end TaftAlgebraType
