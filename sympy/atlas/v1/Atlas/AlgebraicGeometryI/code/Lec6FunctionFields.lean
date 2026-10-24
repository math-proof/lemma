/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec6FunctionFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.NumberTheory.RamificationInertia.Basic
import Mathlib.CategoryTheory.Yoneda
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.Data.Set.Card
import Mathlib.RingTheory.Discriminant
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nilpotent.Lemmas
import Mathlib.RingTheory.Localization.NormTrace

open CategoryTheory Opposite

noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

example (X : AlgebraicGeometry.Scheme) [IrreducibleSpace X] :
    X.functionField = X.presheaf.stalk (genericPoint X) := rfl

example (X : AlgebraicGeometry.Scheme) [IrreducibleSpace X] (U : X.Opens)
    [Nonempty U] : Algebra Γ(X, U) X.functionField := inferInstance

/-- The function field `K(X)` of an integral scheme `X` is a field
(Lec 6, Def 14 setting). -/
instance functionField_field (X : AlgebraicGeometry.Scheme) [IsIntegral X] :
    Field X.functionField := inferInstance

/-- For affine `Spec R` with `R` a domain, the function field is the
fraction field of `R` (Lec 6, Def 14 in the affine case). -/
instance functionField_isFractionRing_affine (R : CommRingCat) [IsDomain R] :
    IsFractionRing R (AlgebraicGeometry.Spec R).functionField :=
  AlgebraicGeometry.functionField_isFractionRing_of_affine R

/-- The function field of a domain `R`, defined as its fraction field
(Lec 6, Def 14, affine viewpoint). -/
abbrev functionField (R : Type*) [CommRing R] [IsDomain R] : Type _ :=
  FractionRing R

/-- The function field of a domain is a field. -/
instance functionField.field (R : Type*) [CommRing R] [IsDomain R] :
    Field (functionField R) := inferInstance

/-- The domain `R` is an algebra over its function field. -/
instance functionField.algebra (R : Type*) [CommRing R] [IsDomain R] :
    Algebra R (functionField R) := inferInstance

/-- The function field of a domain is its fraction field. -/
instance functionField.isFractionRing (R : Type*) [CommRing R] [IsDomain R] :
    IsFractionRing R (functionField R) := inferInstance

/-- Degree of a dominant map `Spec A → Spec B` of integral affine schemes,
defined as the degree of the corresponding extension of function fields
(Lec 6, Def 15). -/
def degreeDominantMap (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)] :=
  Module.finrank (FractionRing B) (FractionRing A)

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra in
/-- Lec 6, Lem 13: for a finite extension `B → A` with `B` normal,
the number of primes of `A` lying over a prime `𝔭` of `B` is at most the
degree of the corresponding extension of function fields. -/
def Lec6IsUnramifiedOver (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)]
    (𝔭 : Ideal B) : Prop :=
  Set.ncard (Ideal.primesOver 𝔭 A) = Module.finrank (FractionRing B) (FractionRing A)

open Ideal in
/-- A prime `𝔭` of `B` is ramified in `A` if it is not unramified
(Lec 6, Def 16). -/
def Lec6IsRamifiedOver (A B : Type*) [CommRing A] [CommRing B]
    [IsDomain A] [IsDomain B] [Algebra B A]
    [Algebra (FractionRing B) (FractionRing A)]
    (𝔭 : Ideal B) : Prop :=
  ¬ Lec6IsUnramifiedOver A B 𝔭

/-- The ramification locus in `Spec A` of a finite free extension `A → B`,
defined as the zero locus of the discriminant
(Lec 6, Prop 7 setting). -/
def RamificationLocus (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Module.Free A B] : Set (PrimeSpectrum A) :=
  PrimeSpectrum.zeroLocus {Algebra.discr A (Module.Free.chooseBasis A B)}

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding is fully faithful. -/
def yoneda_fully_faithful (C : Type*) [Category C] :
    (coyoneda (C := C)).FullyFaithful :=
  Coyoneda.fullyFaithful

/-- Lec 6, Lem 14 (Yoneda): the coyoneda embedding reflects isomorphisms,
giving an iso `x ≅ y` from any iso of representable functors. -/
def yoneda_injective_on_objects (C : Type*) [Category C]
    {x y : Cᵒᵖ}
    (h : coyoneda.obj x ≅ coyoneda.obj y) :
    x ≅ y :=
  (yoneda_fully_faithful C).preimageIso h

/-- An affine variety `Spec R` is normal if `R` is an integrally closed
domain (Lec 6, normalization). -/
def IsNormalVariety (R : Type*) [CommRing R] [IsDomain R] : Prop :=
  IsIntegrallyClosed R
