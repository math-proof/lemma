/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealFactorization.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.DedekindDomain.Factorization
import Theorem.v1.Atlas.NumberTheoryI.code.IdealFactorization
open scoped nonZeroDivisors
open IsDedekindDomain


noncomputable section IdealFactorization

variable {R : Type*} [CommRing R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]
  [IsDedekindDomain R]

def countFinsupp (I : (FractionalIdeal R⁰ K)ˣ) :
    HeightOneSpectrum R →₀ ℤ :=
  ⟨(FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).toFinset,
    fun v => FractionalIdeal.count K v (I : FractionalIdeal R⁰ K),
    fun _ => (FractionalIdeal.finite_factors (I : FractionalIdeal R⁰ K)).mem_toFinset⟩

end IdealFactorization
