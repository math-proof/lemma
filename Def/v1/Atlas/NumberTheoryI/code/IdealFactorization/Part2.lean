/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part2
open scoped nonZeroDivisors
open IsDedekindDomain


noncomputable section IdealFactorization

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]

def fractionalIdeal_mulEquiv_finsupp :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Multiplicative.ofAdd (countFinsupp K I)
  invFun exps := Units.mk0
    ((Multiplicative.toAdd exps).prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e))
    (finsuppProd_primeIdealPow_ne_zero K (Multiplicative.toAdd exps))
  left_inv I := by
    apply Units.ext
    simp only [Units.val_mk0, toAdd_ofAdd]
    exact finsuppProd_countFinsupp_eq K I
  right_inv exps := by
    rw [show exps = Multiplicative.ofAdd (Multiplicative.toAdd exps) from (ofAdd_toAdd _).symm]
    ext v
    show FractionalIdeal.count K v _ = _
    rw [Units.val_mk0]
    exact FractionalIdeal.count_finsuppProd K v _
  map_mul' I J := by
    rw [← ofAdd_add]
    congr 1
    ext v
    show FractionalIdeal.count K v
        ((I * J : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) +
      FractionalIdeal.count K v (J : FractionalIdeal R⁰ K)
    rw [Units.val_mul]
    exact FractionalIdeal.count_mul K v (Units.ne_zero I) (Units.ne_zero J)

end IdealFactorization
