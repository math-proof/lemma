/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/IdealNorms.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.NumberTheory.KummerDedekind
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.FractionalIdeal.Basic
import Mathlib.RingTheory.FractionalIdeal.Inverse
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
open nonZeroDivisors DirectSum


section LocalModuleIndex

variable {R : Type*} [CommRing R] [IsDomain R]

variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

variable {M : Type*} [AddCommGroup M] [Module R M]

noncomputable def localModuleIndex (φ : M →ₗ[R] M) : FractionalIdeal R⁰ K :=
  FractionalIdeal.spanSingleton R⁰ (algebraMap R K (LinearMap.det φ))

noncomputable def concreteModuleIndex (N : Submodule R M) : ℕ :=
  Nat.card (M ⧸ N)

open Classical in
noncomputable def dedekind_kummer_bijection
    (hI : I.IsMaximal) (hI' : I ≠ ⊥)
    (hx : (conductor R x).comap (algebraMap R S) ⊔ I = ⊤)
    (hx' : IsIntegral R x) :
    {J : Ideal S | J ∈ normalizedFactors (I.map (algebraMap R S))} ≃
      {d : (R ⧸ I)[X] |
        d ∈ normalizedFactors (Polynomial.map (Ideal.Quotient.mk I) (minpoly R x))} :=
  KummerDedekind.normalizedFactorsMapEquivNormalizedFactorsMinPolyMk hI hI' hx hx'

noncomputable def idealNorm : Ideal B →*₀ Ideal A := Ideal.relNorm A

end LocalModuleIndex
