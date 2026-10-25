/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/

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
import Theorem.v1.Atlas.TensorCategories.code.SweedlerConcrete.Part3
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- The standard basis vector `e i` of `SweedlerH4 k`, with coefficient `1` at `i` and `0`
elsewhere. -/
def e (i : Fin 4) : SweedlerH4 k where
  coeff := fun j => if i = j then 1 else 0

/-- The Sweedler generator `g`, identified with the basis vector `e 1`. -/
def gen_g : SweedlerH4 k := e 1

/-- The Sweedler generator `x`, identified with the basis vector `e 2`. -/
def gen_x : SweedlerH4 k := e 2

end SweedlerH4
