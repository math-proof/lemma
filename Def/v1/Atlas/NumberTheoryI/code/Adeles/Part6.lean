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
public import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
public import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.Adeles.Part4


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

noncomputable def finAdeleRing_baseChangeHom (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    FiniteAdeleRing (𝓞 K) K →ₐ[K] FiniteAdeleRing (𝓞 L) L where
  toFun a := RestrictedProduct.mk
    (fun w => (baseChangeAtPrime K L w) (a (primeBelow K L w)))
    (baseChange_restricted_condition K L a)
  map_one' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (1 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 1 from rfl, map_one]
    rfl
  map_mul' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a * b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) * b (primeBelow K L w) from rfl, map_mul]
    rfl
  map_zero' := by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (0 : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) = 0 from rfl, map_zero]
    rfl
  map_add' := fun a b => by
    apply RestrictedProduct.ext; intro w
    simp only [RestrictedProduct.mk_apply]
    simp only [show (a + b : FiniteAdeleRing (𝓞 K) K) (primeBelow K L w) =
      a (primeBelow K L w) + b (primeBelow K L w) from rfl, map_add]
    rfl
  commutes' := fun k => baseChange_commutes K L k

def finAdeleRing_includeExt (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] :
    L →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  (Algebra.ofId L (FiniteAdeleRing (𝓞 L) L)).restrictScalars K

def finAdeleRing_tensor_forward (K L : Type*) [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L] :
    (FiniteAdeleRing (𝓞 K) K ⊗[K] L) →ₐ[K] FiniteAdeleRing (𝓞 L) L :=
  Algebra.TensorProduct.lift (finAdeleRing_baseChangeHom K L)
    (finAdeleRing_includeExt K L) (fun _ _ => Commute.all _ _)

end RestrictedProductDirectLimit
end NumberField.Adeles
end
