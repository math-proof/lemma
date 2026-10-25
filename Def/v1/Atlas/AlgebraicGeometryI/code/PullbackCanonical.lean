/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/PullbackCanonical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.RingTheory.FractionalIdeal.Extended
import Mathlib.RingTheory.Ideal.Norm.RelNorm
import Mathlib.RingTheory.FractionalIdeal.Norm
import Mathlib.LinearAlgebra.Dimension.Finrank
set_option linter.unusedSectionVars false

open scoped nonZeroDivisors


namespace PullbackCanonical

section PullbackDef

variable (R : Type*) [CommRing R] [IsDomain R] [IsDedekindDomain R]

variable (S : Type*) [CommRing S] [IsDomain S] [IsDedekindDomain S]

variable [Algebra R S] [Module.IsTorsionFree R S]

variable (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K]

variable (L : Type*) [Field L] [Algebra S L] [IsFractionRing S L]

/-- The pullback ring homomorphism on fractional ideals along `R → S`: extension of
scalars from fractional ideals in the fraction field `K` of `R` to fractional ideals
in the fraction field `L` of `S`. -/
noncomputable def pullbackDivisor :
    FractionalIdeal R⁰ K →+* FractionalIdeal S⁰ L :=
  FractionalIdeal.extendedHomₐ L S

/-- The degree `[Frac S : Frac R]` of the field extension of fraction fields. -/
noncomputable def extensionDegree : ℕ := by
  letI : Algebra (FractionRing R) (FractionRing S) := FractionRing.liftAlgebra R _
  exact Module.finrank (FractionRing R) (FractionRing S)

end PullbackDef
end PullbackCanonical
