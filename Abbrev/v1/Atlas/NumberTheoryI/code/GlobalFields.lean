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
public import Def.v1.Atlas.NumberTheoryI.code.GlobalFields.Part5


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

section RealComplexEmbeddings

variable {K : Type*} [Field K]

abbrev IsRealEmbedding (φ : K →+* ℂ) : Prop := ComplexEmbedding.IsReal φ

abbrev IsComplexEmbedding (φ : K →+* ℂ) : Prop := ¬ ComplexEmbedding.IsReal φ

end RealComplexEmbeddings
end
