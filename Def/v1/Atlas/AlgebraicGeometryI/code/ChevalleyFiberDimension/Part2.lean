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
import Structure.v1.Atlas.AlgebraicGeometryI.code.ChevalleyFiberDimension


noncomputable section

open PrimeSpectrum Topology

namespace ChevalleyFiberDim

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

end ChevalleyFiberDim
end
