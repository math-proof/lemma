/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/

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
public import Mathlib.Algebra.FreeAlgebra
public import Mathlib.Algebra.RingQuot
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Def.v1.Atlas.TensorCategories.code.QuantumSl2.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuantumSl2
public import Structure.v1.Atlas.TensorCategories.code.QuantumSl2Concrete

@[expose] public section

variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- Zero element: the all-zero coefficient vector. -/
noncomputable instance : Zero (SmallQuantumSl2 n k) := ⟨⟨0⟩⟩

/-- Coefficient-wise addition. -/
noncomputable instance : Add (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩

/-- Coefficient-wise negation. -/
noncomputable instance : Neg (SmallQuantumSl2 n k) := ⟨fun a => ⟨-a.coeff⟩⟩

/-- Coefficient-wise subtraction. -/
noncomputable instance : Sub (SmallQuantumSl2 n k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩

/-- Scalar multiplication by `k` on coefficients. -/
noncomputable instance instSMul : SMul k (SmallQuantumSl2 n k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

end SmallQuantumSl2
