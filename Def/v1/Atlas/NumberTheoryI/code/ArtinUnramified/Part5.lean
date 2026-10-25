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
import Instance.v1.Atlas.NumberTheoryI.code.ArtinUnramified


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
