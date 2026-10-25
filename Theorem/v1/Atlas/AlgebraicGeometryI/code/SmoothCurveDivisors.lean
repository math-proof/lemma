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
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothCurveDivisors


noncomputable section

open IsDedekindDomain

namespace SmoothCurveDivisors

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]


/-- Two non-zero fractional ideals with the same valuation at every height-one
prime are equal — unique factorization for Dedekind domains. -/
lemma eq_of_count_eq {I J : FractionalIdeal (nonZeroDivisors R) K}
    (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, FractionalIdeal.count K v I = FractionalIdeal.count K v J) :
    I = J := by
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hJ]
  congr 1; funext v; exact congrArg _ (h v)

/-- Left-inverse: rebuilding a fractional ideal from its valuation vector recovers
the original ideal. -/
lemma bwd_fwd (I : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    bwdFun R K (fwdFun R K I) = I := by
  ext1
  simp only [bwdFun, Units.val_mk0]
  apply eq_of_count_eq R K
  · rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ =>
      zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr v.ne_bot)
  · exact Units.ne_zero I
  · intro v
    rw [FractionalIdeal.count_finsuppProd]
    simp [fwdFun]

/-- Right-inverse: reading off the valuation vector of the ideal `∏ Pᵥ^{nᵥ}`
gives back `(nᵥ)`. -/
lemma fwd_bwd (f : HeightOneSpectrum R →₀ ℤ) :
    fwdFun R K (bwdFun R K f) = f := by
  ext v
  simp only [fwdFun, Finsupp.coe_mk, bwdFun, Units.val_mk0]
  exact FractionalIdeal.count_finsuppProd K v f

/-- Multiplicativity of the divisor map: `div(I · J) = div(I) + div(J)`. -/
lemma fwd_mul (I J : (FractionalIdeal (nonZeroDivisors R) K)ˣ) :
    fwdFun R K (I * J) = fwdFun R K I + fwdFun R K J := by
  ext v
  simp only [fwdFun, Finsupp.coe_mk, Finsupp.add_apply, Units.val_mul]
  exact FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)

end SmoothCurveDivisors
end
