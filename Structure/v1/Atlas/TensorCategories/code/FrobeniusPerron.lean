/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FrobeniusPerron.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Mathlib.Data.Complex.Basic
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings
public import Def.v1.Atlas.TensorCategories.code.PerronFrobeniusProof.Part2
public import Theorem.Category.Atlas.v1.TensorCategories.code.PerronFrobeniusProof
public section

set_option maxHeartbeats 400000


structure FusionRing (ι : Type*) [DecidableEq ι] [Fintype ι] where
  unit : ι
  N : ι → ι → ι → ℕ
  star : ι → ι
  star_star : ∀ i, star (star i) = i
  unit_mul : ∀ j k, N unit j k = if j = k then 1 else 0
  mul_unit : ∀ i k, N i unit k = if i = k then 1 else 0
  duality : ∀ i j, N i j unit = if j = star i then 1 else 0
  assoc : ∀ i j k l, ∑ m : ι, N i j m * N m k l = ∑ m : ι, N j k m * N i m l
  N_star_transpose : ∀ i j k, N i j k = N (star i) k j

