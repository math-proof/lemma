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
import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part3
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

variable [Fact (q ^ n = 1)]

/-- The basis element `e ij ∈ TaftAlgebraType n q k` corresponding to the basis vector `g^{i_1}
x^{i_2}`. -/
def e (ij : Fin n × Fin n) : TaftAlgebraType n q k where
  coeff := fun p => if ij = p then 1 else 0

/-- The generator `g` of the Taft algebra, equal to the basis element `e (1, 0)`. -/
def gen_g (hn2 : n ≥ 2) : TaftAlgebraType n q k :=
  e (⟨1, by omega⟩, ⟨0, NeZero.pos n⟩)

/-- The generator `x` of the Taft algebra, equal to the basis element `e (0, 1)`. -/
def gen_x (hn2 : n ≥ 2) : TaftAlgebraType n q k :=
  e (⟨0, NeZero.pos n⟩, ⟨1, by omega⟩)

end TaftAlgebraType
