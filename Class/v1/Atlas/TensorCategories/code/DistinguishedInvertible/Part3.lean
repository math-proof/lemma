module

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/DistinguishedInvertible.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Limits.Preserves.Finite
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.CategoryTheory.Yoneda
public import Instance.v1.Atlas.TensorCategories.code.InvertibleObjects
public import Structure.v1.Atlas.TensorCategories.code.PivotalSpherical.Part3
public import Def.v1.Atlas.TensorCategories.code.CategoricalFreeness.Part2
public import Def.v1.Atlas.TensorCategories.code.DistinguishedInvertible.Part4
public section
set_option maxHeartbeats 800000

open CategoryTheory MonoidalCategory Category Limits TensorCategories

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]

namespace HasDistinguishedInvertible

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RigidCategory C]
  [HasDistinguishedInvertibleData C]

open scoped TensorProduct in
/-- A quasi-Hopf algebra over `k`: an algebra `H` equipped with a coproduct, counit, an
invertible associator `Φ`, an antipode together with elements `α, β ∈ H`, and a left
`H`-module structure on the linear dual `H^*`. -/
class IsQuasiHopfAlgebra (k : Type*) (H : Type*) [Field k] [Ring H] [Algebra k H] where
  comul : H →ₐ[k] H ⊗[k] H
  counit : H →ₐ[k] k
  rTensor_counit_comp_comul :
    counit.toLinearMap.rTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k k H) 1
  lTensor_counit_comp_comul :
    counit.toLinearMap.lTensor H ∘ₗ comul.toLinearMap = (TensorProduct.mk k H k).flip 1
  Φ : H ⊗[k] H ⊗[k] H
  Φ_invertible : ∃ Ψ : H ⊗[k] H ⊗[k] H, Φ * Ψ = 1 ∧ Ψ * Φ = 1
  antipode : H ≃ₗ[k] H
  antipode_anti_mul : ∀ x y : H, antipode (x * y) = antipode y * antipode x
  antipode_one : antipode 1 = 1
  α : H
  β : H
  leftModuleDual : Module H (Module.Dual k H)

end HasDistinguishedInvertible
end CategoryTheory
