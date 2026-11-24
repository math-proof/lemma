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
public import Def.v1.Atlas.TensorCategories.code.QuantumSl2Concrete


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/QuantumSl2Concrete.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
variable {n : ℕ} {k : Type*} [Field k]


namespace SmallQuantumSl2

/-- `SmallQuantumSl2 n k` is a finite `k`-module. -/
noncomputable instance : Module.Finite k (SmallQuantumSl2 n k) :=
  Module.Finite.equiv toFunEquiv.symm

/-- `SmallQuantumSl2 n k` is finite-dimensional over `k`. -/
instance finiteDimensional : FiniteDimensional k (SmallQuantumSl2 n k) := inferInstance

end SmallQuantumSl2
