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
public import Def.v1.Atlas.TensorCategories.code.TaftConcrete.Part2


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

/-- The unit element `1` of `TaftAlgebraType`: the indicator function of the origin index. -/
noncomputable instance : One (TaftAlgebraType n q k) where
  one := ⟨fun ij => if ij = zp then 1 else 0⟩

/-- The natural-number cast in `TaftAlgebraType` lives entirely at the origin index. -/
noncomputable instance : NatCast (TaftAlgebraType n q k) where
  natCast c := ⟨fun ij => if ij = zp then (c : k) else 0⟩

/-- The integer cast in `TaftAlgebraType` lives entirely at the origin index. -/
noncomputable instance : IntCast (TaftAlgebraType n q k) where
  intCast c := ⟨fun ij => if ij = zp then (c : k) else 0⟩

end TaftAlgebraType
