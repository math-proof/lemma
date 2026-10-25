/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
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

end ChevalleyFiberDim
end
