/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/

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
public import Mathlib.Data.Fintype.Prod
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Structure.v1.Atlas.TensorCategories.code.TaftConcrete

@[expose] public section

variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- The zero element of `TaftAlgebraType` has all coefficients equal to zero. -/
noncomputable instance : Zero (TaftAlgebraType n q k) := ⟨⟨0⟩⟩

/-- Pointwise addition of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Add (TaftAlgebraType n q k) := ⟨fun a b => ⟨a.coeff + b.coeff⟩⟩

/-- Pointwise negation of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Neg (TaftAlgebraType n q k) := ⟨fun a => ⟨-a.coeff⟩⟩

/-- Pointwise subtraction of coefficient vectors in `TaftAlgebraType`. -/
noncomputable instance : Sub (TaftAlgebraType n q k) := ⟨fun a b => ⟨a.coeff - b.coeff⟩⟩

/-- Pointwise scalar multiplication by `k` on `TaftAlgebraType`. -/
noncomputable instance instSMul : SMul k (TaftAlgebraType n q k) := ⟨fun r a => ⟨r • a.coeff⟩⟩

end TaftAlgebraType
