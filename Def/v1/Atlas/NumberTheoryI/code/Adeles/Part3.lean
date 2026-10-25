/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Adeles.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.ProductFormula
import Mathlib.Topology.Algebra.Group.Compact
import Mathlib.Topology.Algebra.Valued.LocallyCompact
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.RingTheory.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Free
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.ConvexBody
import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.AdicCompletionAlgebra
import Theorem.v1.Atlas.NumberTheoryI.code.AdicCompletionAlgebra.Part3
import Instance.v1.Atlas.NumberTheoryI.code.Adeles.Part5


noncomputable section

open NumberField IsDedekindDomain

open scoped TensorProduct

namespace NumberField.Adeles

variable {K : Type*} [Field K] [NumberField K]

section RestrictedProductDirectLimit

open Filter Set Topology

attribute [local instance] WithAbs.algebraLeft

set_option backward.isDefEq.respectTransparency false in
noncomputable def tensorCompletionToFiberProd
    (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
    (v : InfinitePlace K) :
    L ⊗[K] v.Completion →+*
      ((w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) := by
  apply Pi.ringHom
  intro ⟨w, hw⟩
  letI : Algebra K w.Completion := Algebra.restrictScalars K L w.Completion
  haveI : IsScalarTower K L w.Completion := by
    constructor; intro x y z; change (x • y) • z = x • (y • z); simp [smul_assoc]
  haveI : w.1.LiesOver v.1 := ⟨by
    have h1 : (w.comap (algebraMap K L)).1 = v.1 := by rw [hw]
    rw [← h1]; rfl⟩
  haveI itv : IsTopologicalRing (WithAbs v.1) := inferInstance
  haveI itw : IsTopologicalRing (WithAbs w.1) := inferInstance
  haveI uv : IsUniformAddGroup (WithAbs v.1) := inferInstance
  haveI uw : IsUniformAddGroup (WithAbs w.1) := inferInstance
  have hiso := InfinitePlace.LiesOver.isometry_algebraMap w (v := v)
  let isoHom : v.Completion →+* w.Completion :=
    @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
      (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
  let vToW : v.Completion →ₐ[K] w.Completion := {
    toRingHom := isoHom
    commutes' := by
      intro r
      change @Isometry.mapRingHom _ _ _ _ itv uv _ _ uw itw
        (algebraMap (WithAbs v.1) (WithAbs w.1)) hiso
        (↑(algebraMap K (WithAbs v.1) r)) = algebraMap K w.Completion r
      rw [@Isometry.mapRingHom_coe _ _ _ _ itv uv _ _ uw itw _ hiso]
      congr 1
  }
  let lToW : L →ₐ[K] w.Completion := {
    toRingHom := algebraMap L w.Completion
    commutes' := fun _ => rfl
  }
  exact (Algebra.TensorProduct.productMap lToW vToW).toRingHom


def sigmaPiRegroup (K L : Type*) [Field K] [Field L] [Algebra K L] :
    ((v : InfinitePlace K) →
      (w : { w : InfinitePlace L // w.comap (algebraMap K L) = v }) → w.val.Completion) ≃+*
    InfiniteAdeleRing L :=
  RingEquiv.mk
    { toFun := fun g w => g (w.comap (algebraMap K L)) ⟨w, rfl⟩
      invFun := fun h _v ⟨w, _⟩ => h w
      left_inv := fun g => by ext v ⟨w, hw⟩; subst hw; rfl
      right_inv := fun _ => rfl }
    (fun _ _ => rfl) (fun _ _ => rfl)

end RestrictedProductDirectLimit
end NumberField.Adeles
end
