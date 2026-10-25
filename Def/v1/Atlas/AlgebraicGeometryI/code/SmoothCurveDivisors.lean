/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothCurveDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.ClassGroup
import Mathlib.RingTheory.PicardGroup
import Abbrev.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors


noncomputable section

open IsDedekindDomain

namespace SmoothCurveDivisors

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


/-- For a fractional ideal `I`, only finitely many height-one primes appear
non-trivially in the factorization. -/
def countFinite (I : FractionalIdeal (nonZeroDivisors R) K) :
    {v : HeightOneSpectrum R | FractionalIdeal.count K v I ≠ 0}.Finite := by
  have h := FractionalIdeal.finite_factors I
  rwa [Filter.eventually_cofinite] at h

/-- **Divisor of a fractional ideal**: sends an invertible fractional ideal `I` to
its formal sum of valuations `Σ v_P(I) · [P]` over height-one primes `P`. -/
def fwdFun (I : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    HeightOneSpectrum R →₀ ℤ where
  toFun := fun v => FractionalIdeal.count K v (I : FractionalIdeal (nonZeroDivisors R) K)
  support := (countFinite R K I).toFinset
  mem_support_toFun := by intro v; simp [Set.Finite.mem_toFinset]

/-- **Fractional ideal from a divisor**: sends a finitely supported `f : v ↦ nᵥ`
to the product `∏ᵥ Pᵥ^{nᵥ}`, the corresponding invertible fractional ideal. -/
def bwdFun (f : HeightOneSpectrum R →₀ ℤ) :
    (FractionalIdeal (nonZeroDivisors R) K)ˣ :=
  Units.mk0 (f.prod (fun v n => (v.asIdeal : FractionalIdeal (nonZeroDivisors R) K) ^ n))
    (by
      rw [Finsupp.prod]
      exact Finset.prod_ne_zero_iff.mpr fun v _ =>
        zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot))

end SmoothCurveDivisors
end
