module
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Def.v1.Atlas.TensorCategories.code.SweedlerConcrete


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
