module
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.NumberTheory.NumberField.Norm
public import Mathlib.NumberTheory.NumberField.ClassNumber
public import Mathlib.NumberTheory.NumberField.Units.Basic
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
public import Mathlib.GroupTheory.FiniteAbelian.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.NumberField.InfinitePlace.Ramification
public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.GroupTheory.Index
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.Hilbert90
public import Theorem.Set.Closure.eq.N.of.Eq
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Ideal.Norm.RelNorm
public import Mathlib.RingTheory.FractionalIdeal.Extended
public import Mathlib.RingTheory.Invariant.Basic
public import Theorem.Nat.Atlas.v1.NumberTheoryI.code.Lemma247
public import Instance.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ArtinUnramified.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
noncomputable section

open scoped Pointwise

open NumberField

namespace ArtinUnramified

attribute [instance] CyclicExtensionData.instGroupG
  CyclicExtensionData.instFiniteG CyclicExtensionData.instCyclicG
  CyclicExtensionData.instCommGroupM CyclicExtensionData.instFiniteM
  CyclicExtensionData.instAction

noncomputable def herbrandQuotientUnitsValue [Fintype (L ≃ₐ[K] L)]
    [IsCyclic (L ≃ₐ[K] L)] : ℚ :=
  (Nat.card (tateH0Units K L) : ℚ) / (Nat.card (tateMinus1Units K L) : ℚ)

end GaloisUnitsAction

noncomputable def algebraMapToFixed
    (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    (𝓞 K)ˣ →* ↥(unitsFixed K L) where
  toFun v := ⟨Units.map (algebraMap (𝓞 K) (𝓞 L)).toMonoidHom v, fun σ => by
    apply Units.val_injective
    show (galRestrict (𝓞 K) K L (𝓞 L) σ) ((algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)) =
         (algebraMap (𝓞 K) (𝓞 L)) (v : 𝓞 K)
    exact (galRestrict (𝓞 K) K L (𝓞 L) σ).commutes (v : 𝓞 K)⟩
  map_one' := by ext; simp
  map_mul' v w := by ext; simp

end
