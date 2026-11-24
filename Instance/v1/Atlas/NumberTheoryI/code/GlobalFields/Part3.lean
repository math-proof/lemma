module
public import Mathlib.NumberTheory.NumberField.Discriminant.Basic
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
public import Mathlib.NumberTheory.NumberField.InfiniteAdeleRing
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.Artinian.Module
public import Theorem.v1.Atlas.NumberTheoryI.code.CompleteFields.Part2
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.CompleteFields
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Def.v1.Atlas.NumberTheoryI.code.GlobalFields.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/GlobalFields.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField NumberField.InfinitePlace Module Fintype IsDedekindDomain

section TensorProductDecomposition

set_option maxHeartbeats 2000000

set_option synthInstance.maxHeartbeats 80000

instance nontriviallyNormedField_infinitePlace_completion {K : Type*} [Field K] [NumberField K]
    (v : NumberField.InfinitePlace K) : NontriviallyNormedField v.Completion := by
  constructor; use 2
  have h1 : Completion.extensionEmbedding v 2 = (2 : ℂ) := by simp [map_ofNat]
  have h2 : ‖(2 : v.Completion)‖ = ‖(2 : ℂ)‖ := by
    rw [← h1]
    exact ((Completion.isometry_extensionEmbedding v).norm_map_of_map_zero (map_zero _) 2).symm
  rw [h2]; norm_num

end TensorProductDecomposition
end
