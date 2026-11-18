/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/IntegralsDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.SimpleModule.Basic
public import Class.v1.Atlas.TensorCategories.code.IntegralsDefs.Part2
@[expose] public section
set_option maxHeartbeats 400000

set_option autoImplicit false

open Coalgebra
open scoped TensorProduct

universe u v w


section Proposition_1_52_4

open CategoryTheory

variable (k : Type u) [Field k] (H : Type v) [Ring H] [Algebra k H] [Coalgebra k H]

/-- Alias for `Prop1524Data` used when `C = Rep(H)`. -/
abbrev Prop1524RepData := Prop1524Data

end Proposition_1_52_4
