/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage
import Mathlib.RingTheory.Spectrum.Prime.Noetherian

noncomputable section

open PrimeSpectrum Topology

namespace ChevalleyFiberDim

/-- The Krull dimension of the fiber of `Spec A → Spec B` over a prime `q ∈ Spec B`. -/
def fiberKrullDim {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (q : PrimeSpectrum B) : WithBot ℕ∞ :=
  ringKrullDim (A ⧸ (q.asIdeal.map (algebraMap B A)))

/-- The generic point of `Spec B` for an integral domain `B`, given by the zero ideal. -/
def genericPoint (B : Type*) [CommRing B] [IsDomain B] : PrimeSpectrum B :=
  ⟨⊥, Ideal.isPrime_bot⟩

/-- The set of primes `q` in the image of `Spec A → Spec B` whose fiber has dimension at least
`d`; this is the set whose upper semicontinuity is part of Chevalley's theorem. -/
def fiberDimGeInImage {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : ℕ) : Set (PrimeSpectrum B) :=
  {q | q ∈ Set.range (PrimeSpectrum.comap (algebraMap B A)) ∧
    (d : WithBot ℕ∞) ≤ fiberKrullDim (A := A) q}

/-- The bundled data of a dominant morphism of integral schemes of finite type:
the algebra map is injective, the algebra is finite type, and we record the transcendence degree
of the function field extension. -/
structure DominantFiniteTypeMorphism (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B] [Algebra B A] where
  injective : Function.Injective (algebraMap B A)
  finiteType : Algebra.FiniteType B A
  transDeg : ℕ

/-- Noether normalization descent: for a dominant finite-type morphism between integral domains,
after inverting some nonzero `b ∈ B`, the localized algebra `A[b⁻¹]` is finite over a polynomial
ring `B[b⁻¹][x₁,…,xₙ]`, and the basic open `D(b)` lies in the image. -/
structure Lemma33Data (B A : Type*) [CommRing B] [CommRing A] [Algebra B A] where
  b : B
  hb : b ≠ 0
  n : ℕ
  φ : MvPolynomial (Fin n) (Localization.Away b) →+*
      Localization.Away ((algebraMap B A) b)
  φ_finite : φ.Finite
  φ_injective : Function.Injective φ
  φ_compat : φ.comp MvPolynomial.C = Localization.awayMap (algebraMap B A) b
  basicOpen_sub_image :
    (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap B A))

/-- The locus in `Spec B` where the fiber of `Spec A → Spec B` has dimension at least `d`. -/
def fiberDimGe {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    (d : WithBot ℕ∞) : Set (PrimeSpectrum B) :=
  {q | d ≤ fiberKrullDim (A := A) q}

/-- A ring equivalence comparing the iterated fiber `(A/𝔭A)/(q'A)` to the fiber `A/q'A`, used
when comparing fiber dimensions along specializations. -/
noncomputable def doubleQuot_fiber_equiv {B A : Type*} [CommRing B] [CommRing A] [Algebra B A]
    {𝔭 q' : PrimeSpectrum B} (hle : 𝔭.asIdeal ≤ q'.asIdeal) :
    (A ⧸ 𝔭.asIdeal.map (algebraMap B A)) ⧸
      (q'.asIdeal.map (algebraMap B A)).map
        (Ideal.Quotient.mk (𝔭.asIdeal.map (algebraMap B A))) ≃+*
    A ⧸ q'.asIdeal.map (algebraMap B A) :=
  (DoubleQuot.quotQuotEquivQuotSup _ _).trans
    (Ideal.quotEquivOfEq (sup_eq_right.mpr (Ideal.map_mono hle)))
