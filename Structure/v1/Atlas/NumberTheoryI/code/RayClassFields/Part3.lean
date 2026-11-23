/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/RayClassFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import Def.v1.Atlas.NumberTheoryI.code.KroneckerWeber.Part5
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.KroneckerWeber
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.IdealFactorization
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.FinitePlaceAbsValue
public import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part3
public import Theorem.v1.Atlas.NumberTheoryI.code.FinitePlaceAbsValue
public import Def.v1.Atlas.NumberTheoryI.code.RayClassFields.Part11


public noncomputable section

open scoped NumberField

namespace RayClassField

variable {K : Type*} [Field K] [NumberField K]

universe u

structure IsRayClassField (K : Type u) (L : Type u) [Field K] [Field L]
    [NumberField K] [NumberField L] [Algebra K L] [KroneckerWeber.IsAbelianExtension K L]
    (𝔪 : Modulus K) : Prop where
  finiteDimensional : FiniteDimensional K L
  unramified_outside :
    ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      𝔪 (Place.finite 𝔭) = 0 →
      ∀ (𝔔 : Ideal (NumberField.RingOfIntegers L)) [𝔔.IsPrime],
        𝔔.LiesOver 𝔭.asIdeal →
        Algebra.IsUnramifiedAt (NumberField.RingOfIntegers K) 𝔔
  kernel_eq_ray_group :
    MonoidHom.ker (ArtinMap K L 𝔪) = RayGroup K 𝔪

end RayClassField
end
