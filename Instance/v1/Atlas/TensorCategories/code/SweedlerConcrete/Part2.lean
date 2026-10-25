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
import Def.v1.Atlas.TensorCategories.code.SweedlerConcrete
variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Multiplication on `SweedlerH4 k`, given by bilinearly extending the basis structure
constants `basisMul`. -/
noncomputable instance : Mul (SweedlerH4 k) where
  mul a b := ⟨fun m => ∑ i : Fin 4, ∑ j : Fin 4, a.coeff i * b.coeff j * basisMul i j m⟩

/-- The unit element of `SweedlerH4 k`, the basis vector `e₀`. -/
noncomputable instance : One (SweedlerH4 k) where
  one := ⟨fun i => if i = 0 then 1 else 0⟩

/-- The natural-number cast into `SweedlerH4 k`, sending `n` to `n · e₀`. -/
noncomputable instance : NatCast (SweedlerH4 k) where
  natCast n := ⟨fun i => if i = 0 then (n : k) else 0⟩

/-- The integer cast into `SweedlerH4 k`, sending `n` to `n · e₀`. -/
noncomputable instance : IntCast (SweedlerH4 k) where
  intCast n := ⟨fun i => if i = 0 then (n : k) else 0⟩

end SweedlerH4
