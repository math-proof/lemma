/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LocallyFactorialDivisors.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.PID
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.ClassGroup
import Mathlib.Data.Finsupp.Basic
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.GroupTheory.QuotientGroup.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LocallyFactorialDivisors.Part4


noncomputable section

open scoped nonZeroDivisors

open IsDedekindDomain

namespace LocallyFactorialDivisors

attribute [instance] HeightOnePrime.isPrime

/-- A nonzero height-one prime ideal gives a nonzero fractional ideal. -/
lemma height_one_coe_ne_zero (v : HeightOneSpectrum R) :
    (↑v.asIdeal : FractionalIdeal R⁰ K) ≠ 0 := by
  rw [FractionalIdeal.coeIdeal_ne_zero]
  exact v.ne_bot

/-- The fractional ideal coming from a Weil divisor is nonzero. -/
theorem weilToCartierIdeal_ne_zero (D : HeightOneSpectrum R →₀ ℤ) :
    weilToCartierIdeal K D ≠ 0 := by
  unfold weilToCartierIdeal
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr
    (fun v _ => zpow_ne_zero _ (height_one_coe_ne_zero K v))

/-- The Cartier-to-Weil map is surjective: every Weil divisor comes from a Cartier
divisor. -/
theorem cartierToWeil_surjective :
    Function.Surjective (cartierToWeil (R := R) K) := by
  intro D

  let I := weilToCartierIdeal K D
  have hI : I ≠ 0 := weilToCartierIdeal_ne_zero K D

  let u := Units.mk0 I hI
  use u

  ext v
  simp only [cartierToWeil_apply]
  exact FractionalIdeal.count_finsuppProd K v D


end LocallyFactorialDivisors
end
