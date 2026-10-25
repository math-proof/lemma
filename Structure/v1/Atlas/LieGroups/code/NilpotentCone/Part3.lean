/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/NilpotentCone.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Semisimple.Basic
import Mathlib.Algebra.Lie.CartanSubalgebra
import Mathlib.Algebra.Lie.Sl2
import Mathlib.Algebra.Lie.Rank
import Mathlib.Algebra.Lie.CartanExists
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Topology.Basic
import Mathlib.Topology.Irreducible
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Def.v1.Atlas.LieGroups.code.NilpotentCone.Part3


noncomputable section

open scoped LieAlgebra

open Set

namespace LieAlgebra

variable (R : Type*) [CommRing R]

variable (L : Type*) [LieRing L] [LieAlgebra R L]

variable {R L}

variable [Module.Finite R L] [Module.Free R L]

section PrincipalSl2

variable {𝔤 : Type*} [LieRing 𝔤] [LieAlgebra ℂ 𝔤]
  [LieAlgebra.IsSemisimple ℂ 𝔤]
  [Module.Finite ℂ 𝔤] [Module.Free ℂ 𝔤]

structure NilpotentConeCoordinateRing [LieAlgebra.IsSemisimple ℂ 𝔤] where
  carrier : Type*
  instCommRing : CommRing carrier
  instAlgebra : Algebra ℂ carrier
  instNontrivial : Nontrivial carrier
  genericFiber : Type*
  instGenericFiberCommRing : CommRing genericFiber
  toGenericFiber : @RingHom carrier genericFiber
    instCommRing.toNonAssocRing.toNonAssocSemiring
    instGenericFiberCommRing.toNonAssocRing.toNonAssocSemiring
  instCarrierGenericFiberAlg : @Algebra carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
  locSubmonoid : @Submonoid carrier instCommRing.toMulOneClass
  locSubmonoid_le_nonZeroDivisors :
    ∀ s ∈ locSubmonoid, s ∈ @nonZeroDivisors carrier instCommRing.toMonoidWithZero
  instIsLocalization : @IsLocalization carrier instCommRing.toCommSemiring
    locSubmonoid genericFiber instGenericFiberCommRing.toCommSemiring
    instCarrierGenericFiberAlg
  toGenericFiber_eq : toGenericFiber = @algebraMap carrier genericFiber
    instCommRing.toCommSemiring instGenericFiberCommRing.toSemiring
    instCarrierGenericFiberAlg
  instGenericFiberSemisimple : @IsSemisimpleRing genericFiber
    instGenericFiberCommRing.toRing

end PrincipalSl2
end LieAlgebra
end
