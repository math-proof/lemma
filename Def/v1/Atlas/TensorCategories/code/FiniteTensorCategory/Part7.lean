/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/FiniteTensorCategory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Simple
public import Mathlib.CategoryTheory.Preadditive.Schur
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.Bialgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiBialgebra
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.FGModuleCat.Abelian
public import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Module.Projective
public import Abbrev.v1.Atlas.TensorCategories.code.QuasiTensorFunctor.Part5
public import Theorem.Category.Atlas.v1.TensorCategories.code.QuasiTensorFunctor

@[expose] public section
set_option maxHeartbeats 800000

open scoped TensorProduct

namespace CategoryTheory

open TensorCategories

/-- C admits a quasi-fiber functor to ModuleCat k. -/
def HasQuasiFiberFunctor (k : Type w) [Field k]
    (C : Type u) [Category.{v} C] [MonoidalCategory C] [Abelian C] : Prop :=
  Nonempty (QuasiFiberFunctor k C)

/-- If C admits a quasi-fiber functor, then every FP-dimension function on C is
integral (EGNO Theorem 1.45). -/
def QuasiHopfTwistIsoEquiv
    (k : Type u) [Field k]
    (H₁ : Type u) [Ring H₁] [Algebra k H₁] [QuasiHopfAlgebra k H₁]
    (H₂ : Type u) [Ring H₂] [Algebra k H₂] [QuasiHopfAlgebra k H₂] : Prop :=
  ∃ (φ : H₁ ≃ₐ[k] H₂) (J : (H₂ ⊗[k] H₂)ˣ),

    (∀ x : H₂,
      QuasiBialgebra.counit (R := k) (H := H₂) x =
      QuasiBialgebra.counit (R := k) (H := H₁) (φ.symm x)) ∧


    (∀ x : H₂,
      (QuasiBialgebra.comul (R := k) (H := H₂)) x =
      (↑J⁻¹ : H₂ ⊗[k] H₂) *
      (Algebra.TensorProduct.map (φ : H₁ →ₐ[k] H₂) (φ : H₁ →ₐ[k] H₂))
        ((QuasiBialgebra.comul (R := k) (H := H₁)) (φ.symm x)) *
      (↑J : H₂ ⊗[k] H₂))

end CategoryTheory
