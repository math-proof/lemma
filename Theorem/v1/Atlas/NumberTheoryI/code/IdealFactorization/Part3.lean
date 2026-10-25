/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Def.v1.Atlas.NumberTheoryI.code.IdealFactorization.Part2
open scoped nonZeroDivisors
open IsDedekindDomain


noncomputable section IdealFactorization

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]

theorem fractionalIdeal_mulEquiv_finsupp_apply (I : (FractionalIdeal R⁰ K)ˣ)
    (v : HeightOneSpectrum R) :
    (Multiplicative.toAdd (fractionalIdeal_mulEquiv_finsupp K I)) v =
      FractionalIdeal.count K v (I : FractionalIdeal R⁰ K) := by
  simp only [fractionalIdeal_mulEquiv_finsupp, MulEquiv.coe_mk, Equiv.coe_fn_mk, toAdd_ofAdd]
  rfl

theorem fractionalIdeal_mulEquiv_finsupp_symm_apply (exps : HeightOneSpectrum R →₀ ℤ) :
    ((fractionalIdeal_mulEquiv_finsupp K).symm (Multiplicative.ofAdd exps) :
      FractionalIdeal R⁰ K) =
      exps.prod (fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) := by
  simp only [fractionalIdeal_mulEquiv_finsupp, MulEquiv.symm_mk, MulEquiv.coe_mk,
    Equiv.coe_fn_symm_mk, toAdd_ofAdd, Units.val_mk0]

end IdealFactorization
