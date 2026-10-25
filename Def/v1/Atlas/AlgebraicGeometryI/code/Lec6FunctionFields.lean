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
import Instance.v1.Atlas.AlgebraicGeometryI.code.Lec6FunctionFields.Part2
open CategoryTheory Opposite


noncomputable section

namespace Lec6

open AlgebraicGeometry TopologicalSpace

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

end Lec6
end
