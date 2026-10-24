/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/UnivEnvelopingAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.LieGroups.code.SmoothVectors
import Lemma.Real.GetToMonoidHom.in.SmoothSubspace.of.In_SmoothSubspace
import Lemma.Complex.IsStronglyContinuousToMonoidHom
import sympy.atlas.v1.Atlas.LieGroups.code.ContinuousRep
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.Killing
import Mathlib.RingTheory.SimpleModule.Basic
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.FieldTheory.IsAlgClosed.Spectrum

noncomputable section

namespace UnivEnvelopingAction

section ExtendToUEA

variable {R : Type*} [CommRing R]
variable {L : Type*} [LieRing L] [LieAlgebra R L]
variable {V : Type*} [AddCommGroup V] [Module R V]

def extendToUEA (f : L →ₗ⁅R⁆ Module.End R V) :
    UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V :=
  UniversalEnvelopingAlgebra.lift R f

end ExtendToUEA

abbrev CenterUEA (R : Type*) [CommRing R] (L : Type*) [LieRing L] [LieAlgebra R L] :
    Subalgebra R (UniversalEnvelopingAlgebra R L) :=
  Subalgebra.center R (UniversalEnvelopingAlgebra R L)

def ActsByScalar {V : Type*} [AddCommGroup V] [Module R V]
    (φ : UniversalEnvelopingAlgebra R L →ₐ[R] Module.End R V)
    (z : UniversalEnvelopingAlgebra R L) (c : R) : Prop :=
  φ z = c • LinearMap.id

structure InfinitesimalCharacter where
  toAlgHom : CenterUEA R L →ₐ[R] R

def InfinitesimalCharacter.apply (χ : InfinitesimalCharacter R L) (z : CenterUEA R L) : R :=
  χ.toAlgHom z

end InfinitesimalCharacter

section CenterActsByScalar

variable (R : Type*) [Field R] [IsAlgClosed R]
variable (L : Type*) [LieRing L] [LieAlgebra R L]

structure IsKillingDualBasis (b d : ι → L) : Prop where
  orthonormal : ∀ i j : ι, killingForm R L (b i) (d j) = if i = j then 1 else 0
  expand_b : ∀ y : L, y = ∑ i : ι, (killingForm R L y (d i)) • (b i)
  expand_d : ∀ y : L, y = ∑ i : ι, (killingForm R L (b i) y) • (d i)

def casimirElement (b d : ι → L) : UniversalEnvelopingAlgebra R L :=
  ∑ i : ι, (UniversalEnvelopingAlgebra.ι R (b i)) * (UniversalEnvelopingAlgebra.ι R (d i))
