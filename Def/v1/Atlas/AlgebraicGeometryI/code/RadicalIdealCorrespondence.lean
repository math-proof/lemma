/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/RadicalIdealCorrespondence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
open PrimeSpectrum Ideal


noncomputable section

section GaloisConnection

variable (R : Type*) [CommSemiring R]

/-- The order-embedding `closeds(Spec R) ↪ Ideal R` provided by the radical
ideal correspondence (Thm 1.2), packaged as an `OrderEmbedding`. -/
def closedsEmbedding :
    (TopologicalSpace.Closeds (PrimeSpectrum R))ᵒᵈ ↪o Ideal R :=
  PrimeSpectrum.closedsEmbedding R

end GaloisConnection
end
