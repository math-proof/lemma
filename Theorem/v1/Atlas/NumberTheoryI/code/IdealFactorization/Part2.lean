/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Def.v1.Atlas.NumberTheoryI.code.IdealFactorization
open scoped nonZeroDivisors
open IsDedekindDomain


noncomputable section IdealFactorization

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]

lemma finsuppProd_countFinsupp_eq (I : (FractionalIdeal R⁰ K)ˣ) :
    (countFinsupp K I).prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) =
      (I : FractionalIdeal R⁰ K) := by
  have hI : (I : FractionalIdeal R⁰ K) ≠ 0 := Units.ne_zero I
  rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K hI,
      Finsupp.prod, countFinsupp]
  simp only [Finsupp.coe_mk]
  symm
  apply finprod_eq_finset_prod_of_mulSupport_subset
  intro v hv
  simp only [Finset.mem_coe, Set.Finite.mem_toFinset]
  rw [Function.mem_mulSupport] at hv
  intro h; exact hv (by rw [h, zpow_zero])

end IdealFactorization
