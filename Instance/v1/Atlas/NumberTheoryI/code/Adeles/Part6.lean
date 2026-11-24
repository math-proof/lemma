module
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.NumberField.ProductFormula
public import Mathlib.Topology.Algebra.Group.Compact
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Free
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Topology.Algebra.Module.Equiv
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Def.v1.Atlas.NumberTheoryI.code.Adeles.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

instance finAdeleRing_algebra_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    Algebra K (FiniteAdeleRing (𝓞 L) L) :=
  ((algebraMap L (FiniteAdeleRing (𝓞 L) L)).comp (algebraMap K L)).toAlgebra

instance finAdeleRing_scalarTower_base_base (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K K (FiniteAdeleRing (𝓞 L) L) :=
  ⟨fun r s x => by simp [Algebra.smul_def, mul_assoc]⟩

instance finAdeleRing_scalarTower_base_ext (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    IsScalarTower K L (FiniteAdeleRing (𝓞 L) L) := by
  constructor; intro r l x; simp only [Algebra.smul_def]; rw [map_mul, mul_assoc]; rfl

end RestrictedProductDirectLimit
end NumberField.Adeles
end
