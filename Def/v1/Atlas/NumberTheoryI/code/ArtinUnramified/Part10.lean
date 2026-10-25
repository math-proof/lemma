/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.NumberTheory.NumberField.ClassNumber
import Mathlib.NumberTheory.NumberField.Units.Basic
import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import Mathlib.GroupTheory.FiniteAbelian.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.GroupTheory.Index
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Mathlib.Algebra.Set.Closure.eq.N.of.Eq
import Mathlib.RingTheory.Trace.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Invariant.Basic
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part7


noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

def ClassGroup.normMap (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 K) :=
  QuotientGroup.lift _ (normOnFracUnits K L) (normOnFracUnits_kills_principal K L)

def idealGroupIndex
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] : ℕ :=
  (MonoidHom.range (ClassGroup.normMap K L)).index

noncomputable def CyclicExtensionData.norm_index_IK_ax
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  idealGroupIndex K L

def galUnitsAutHom : (L ≃ₐ[K] L) →* MulAut (𝓞 L)ˣ where
  toFun σ := Units.mapEquiv (galRestrict (𝓞 K) K L (𝓞 L) σ).toRingEquiv
  map_one' := by ext u; simp [Units.mapEquiv, galRestrict]
  map_mul' σ τ := by ext u; simp [Units.mapEquiv, galRestrict]

end ArtinUnramified
end
