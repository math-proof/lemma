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
public import Instance.v1.Atlas.NumberTheoryI.code.ArtinUnramified


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

def classGroupFixed (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] :
    Subgroup (ClassGroup (𝓞 L)) :=
  FixedPoints.subgroup (L ≃ₐ[K] L) (ClassGroup (𝓞 L))

def normImageUnits (K L : Type*) [Field K] [Field L] [Algebra K L] :
    Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map (Algebra.norm K : L →* K)))

noncomputable def normUnitsIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L] : ℕ :=
  (normImageUnits K L).index

def normIntegerUnits (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] : Subgroup (𝓞 K)ˣ :=
  Subgroup.comap (Units.map (algebraMap (𝓞 K) K).toMonoidHom)
    (MonoidHom.range (Units.map ((Algebra.norm K).comp (algebraMap (𝓞 L) L).toMonoidHom)))

noncomputable def principalFixedIndex (K L : Type*) [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [IsGalois K L] [FiniteDimensional K L]
    [IsCyclic (L ≃ₐ[K] L)] : ℕ :=
  (normIntegerUnits K L).index * Module.finrank K L / e_inf K L

end ArtinUnramified
end
