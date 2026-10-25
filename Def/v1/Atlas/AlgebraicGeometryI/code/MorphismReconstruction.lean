/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/MorphismReconstruction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.AlgebraicGeometry.Scheme
open AlgebraicGeometry CategoryTheory


/-- Scheme-theoretic form of Corollary 22 (Lec 17): `Spec A ≅ Spec A'` whenever
`A` and `A'` are normal `B`-algebras with the same fraction field `K`. -/
noncomputable def corollary22_scheme_iso
    (B A A' K : Type) [CommRing B] [IsDomain B]
    [CommRing A] [IsDomain A] [CommRing A'] [IsDomain A']
    [CommRing K] [Algebra B K]
    [Algebra B A] [Algebra.IsIntegral B A] [IsIntegrallyClosed A]
    [Algebra A K] [IsScalarTower B A K]
    [Algebra B A'] [Algebra.IsIntegral B A'] [IsIntegrallyClosed A']
    [Algebra A' K] [IsScalarTower B A' K]
    [IsFractionRing A K] [IsFractionRing A' K] :
    Spec (.of A') ≅ Spec (.of A) := by

  have hA : IsIntegralClosure A B K := by
    constructor
    · exact IsFractionRing.injective A K
    · intro x; constructor
      · intro hx; exact (isIntegrallyClosed_iff K).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩; exact (Algebra.IsIntegral.isIntegral (R := B) y).algebraMap
  have hA' : IsIntegralClosure A' B K := by
    constructor
    · exact IsFractionRing.injective A' K
    · intro x; constructor
      · intro hx; exact (isIntegrallyClosed_iff K).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩; exact (Algebra.IsIntegral.isIntegral (R := B) y).algebraMap

  exact Scheme.Spec.mapIso (IsIntegralClosure.equiv B A K A').toRingEquiv.toCommRingCatIso.op


/-- A smooth complete curve over `k` is reconstructed (up to scheme isomorphism)
from its function field: a `k`-isomorphism `K_X ≃ₐ[k] K_Y` of function fields
induces `Spec A_Y ≅ Spec A_X`. -/
noncomputable def smooth_complete_curve_reconstruction
    (k : Type) [Field k]
    (A_X A_Y : Type) [CommRing A_X] [IsDomain A_X] [CommRing A_Y] [IsDomain A_Y]
    [Algebra k A_X] [Algebra k A_Y]
    [IsIntegrallyClosed A_X] [IsIntegrallyClosed A_Y]
    [Algebra.IsIntegral k A_X] [Algebra.IsIntegral k A_Y]
    (K_X K_Y : Type) [Field K_X] [Field K_Y]
    [Algebra A_X K_X] [IsFractionRing A_X K_X]
    [Algebra A_Y K_Y] [IsFractionRing A_Y K_Y]
    [Algebra k K_X] [IsScalarTower k A_X K_X]
    [Algebra k K_Y] [IsScalarTower k A_Y K_Y]
    (φ : K_X ≃ₐ[k] K_Y) :
    Spec (.of A_Y) ≅ Spec (.of A_X) := by

  letI algAYKX : Algebra A_Y K_X :=
    (φ.symm.toRingHom.comp (algebraMap A_Y K_Y)).toAlgebra

  haveI : IsScalarTower k A_Y K_X := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap k K_X x = φ.symm (algebraMap A_Y K_Y (algebraMap k A_Y x))
    conv_rhs => rw [← IsScalarTower.algebraMap_apply k A_Y K_Y]
    exact (φ.symm.commutes x).symm

  haveI : IsFractionRing A_Y K_X := by
    have e : K_Y ≃ₐ[A_Y] K_X := {
      toFun := φ.symm
      invFun := φ
      left_inv := φ.symm.left_inv
      right_inv := φ.symm.right_inv
      map_mul' := φ.symm.map_mul
      map_add' := φ.symm.map_add
      commutes' := fun _ => rfl
    }
    exact IsLocalization.isLocalization_of_algEquiv (nonZeroDivisors A_Y) e

  have hA_X : IsIntegralClosure A_X k K_X := by
    constructor
    · exact IsFractionRing.injective A_X K_X
    · intro x; constructor
      · intro hx; exact (isIntegrallyClosed_iff K_X).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩; exact (Algebra.IsIntegral.isIntegral (R := k) y).algebraMap

  have hA_Y : IsIntegralClosure A_Y k K_X := by
    constructor
    · exact IsFractionRing.injective A_Y K_X
    · intro x; constructor
      · intro hx; exact (isIntegrallyClosed_iff K_X).mp inferInstance hx.tower_top
      · rintro ⟨y, rfl⟩; exact (Algebra.IsIntegral.isIntegral (R := k) y).algebraMap

  exact Scheme.Spec.mapIso (IsIntegralClosure.equiv k A_X K_X A_Y).toRingEquiv.toCommRingCatIso.op

