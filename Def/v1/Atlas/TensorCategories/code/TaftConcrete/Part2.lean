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
public import Instance.v1.Atlas.TensorCategories.code.TaftConcrete.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftConcrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {k : Type*} [Field k] {n : ℕ} [NeZero n] {q : k}

set_option linter.unusedSectionVars false


namespace TaftAlgebraType

/-- The "origin" `(0, 0)` index, corresponding to the basis element `g^0 x^0 = 1`. -/
def zp : Fin n × Fin n := (⟨0, NeZero.pos n⟩, ⟨0, NeZero.pos n⟩)

end TaftAlgebraType
