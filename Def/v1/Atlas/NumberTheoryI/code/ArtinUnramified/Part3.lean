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
public import Theorem.v1.Atlas.NumberTheoryI.code.ArtinUnramified.Part3


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

section GaloisClassGroupAction

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] [FiniteDimensional K L]

set_option maxHeartbeats 1200000 in
def actOnClassGroup (σ : L ≃ₐ[K] L) :
    ClassGroup (𝓞 L) →* ClassGroup (𝓞 L) where
  toFun c := ClassGroup.mk0 (mapIdealGal K L σ
    (Function.surjInv ClassGroup.mk0_surjective c))
  map_one' := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq (ClassGroup.mk0_surjective (R := 𝓞 L)) 1).trans
          ClassGroup.mk0.map_one.symm),
      (mapIdealGal K L σ).map_one, ClassGroup.mk0.map_one]
  map_mul' c d := by
    rw [mk0_mapIdealGal_congr K L σ
        ((Function.surjInv_eq ClassGroup.mk0_surjective (c * d)).trans
          (show ClassGroup.mk0 (Function.surjInv ClassGroup.mk0_surjective c *
              Function.surjInv ClassGroup.mk0_surjective d) = c * d from by
            rw [ClassGroup.mk0.map_mul, Function.surjInv_eq ClassGroup.mk0_surjective c,
              Function.surjInv_eq ClassGroup.mk0_surjective d]).symm),
      (mapIdealGal K L σ).map_mul, ClassGroup.mk0.map_mul]

end GaloisClassGroupAction
end ArtinUnramified
end
