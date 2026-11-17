/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/SweedlerConcrete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Tactic.FinCases
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Structure.v1.Atlas.TensorCategories.code.SweedlerConcrete

@[expose] public section

variable {k : Type*} [Field k]


namespace SweedlerH4

/-- Zero element of `SweedlerH4 k`, with all coefficients zero. -/
noncomputable instance : Zero (SweedlerH4 k) := ⟨⟨0⟩⟩

/-- Addition on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Add (SweedlerH4 k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩

/-- Negation on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Neg (SweedlerH4 k) := ⟨fun a => ⟨-a.coeff⟩⟩

/-- Subtraction on `SweedlerH4 k`, componentwise on coefficients. -/
noncomputable instance : Sub (SweedlerH4 k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩

/-- Scalar multiplication by `k` on `SweedlerH4 k`, scaling each coefficient. -/
noncomputable instance instSMul : SMul k (SweedlerH4 k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

end SweedlerH4
