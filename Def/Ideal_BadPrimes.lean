module

public import Def.FrobeniusDensity_DegOneAsymptotic
public import Mathlib.RingTheory.DedekindDomain.Factorization
public import Mathlib.RingTheory.UniqueFactorizationDomain.NormalizedFactors
public import Mathlib.Data.ZMod.QuotientRing

@[expose] public section

set_option autoImplicit false

namespace FrobeniusDensity

open NumberField Ideal IsDedekindDomain UniqueFactorizationMonoid

section Ramified

variable {K : Type*} [Field K] [NumberField K]

variable (L : Type*) [Field L] [NumberField L]

noncomputable def badPrimes : Finset ℕ :=
  insert 0 (insert 1 (((finite_setOf_inertia_ne_bot_heightOneSpectrum L).image
    (fun v => Nat.card (ℤ ⧸ v.asIdeal.under ℤ))).toFinset))

end Ramified

section DegOneCount

variable (K : Type*) [Field K] [NumberField K]

omit [NumberField K] in
end DegOneCount


end FrobeniusDensity

end
