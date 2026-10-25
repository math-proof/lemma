/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DedekindExtensions.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.PerfectPairing.Basic
import Mathlib.RingTheory.FractionalIdeal.Operations
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.KrullDimension.Basic
import Mathlib.RingTheory.Spectrum.Prime.RingHom
import Mathlib.NumberTheory.NumberField.Basic
import Def.v1.Atlas.NumberTheoryI.code.Pairings.Part2
import Theorem.v1.Atlas.NumberTheoryI.code.DedekindExtensions
open Module


noncomputable section

section DualColonSubmodule

variable (A : Type*) [CommRing A] [IsDomain A]

variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]

noncomputable def colonToDualMap (M : Submodule A K) :
    colonSubmodule A K M →ₗ[A] Module.Dual A M where
  toFun x :=
    { toFun := fun m => colonToA A K M x m
      map_add' := by
        intro m₁ m₂
        apply IsFractionRing.injective A K
        simp only [map_add, colonToA_spec]
        push_cast; ring
      map_smul' := by
        intro c m
        apply IsFractionRing.injective A K
        simp only [colonToA_spec, smul_eq_mul, map_mul, RingHom.id_apply]
        push_cast; rw [Algebra.smul_def]; ring }
  map_add' := by
    intro x₁ x₂; ext m
    apply IsFractionRing.injective A K
    simp only [LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec, LinearMap.add_apply, map_add]
    push_cast; ring
  map_smul' := by
    intro c x; ext m
    apply IsFractionRing.injective A K
    simp only [LinearMap.coe_mk, AddHom.coe_mk, colonToA_spec, LinearMap.smul_apply,
               smul_eq_mul, map_mul, RingHom.id_apply]
    push_cast; rw [Algebra.smul_def]; ring

end DualColonSubmodule
end
