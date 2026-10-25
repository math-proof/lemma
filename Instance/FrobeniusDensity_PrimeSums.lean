-- Carved from Lemma/Definitions/Def_FrobeniusDensity_PrimeSums.lean: instance decls only.
import Lemma.FrobeniusDensity.BadPrimes
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.RingTheory.DedekindDomain.Factorization
import Def.FrobeniusDensity_PrimeSums

set_option autoImplicit false

open Ideal NumberField Filter Topology Asymptotics IsDedekindDomain
open scoped ENNReal NNReal

namespace FrobeniusDensity

variable (K : Type*) [Field K] [NumberField K]

variable {K}

variable (K)

variable {K}

instance liesOver_ratBelow (v : HeightOneSpectrum (𝓞 K)) :
    v.asIdeal.LiesOver (ratPrimeIdeal (ratBelow v)) :=
  (exists_prime_liesOver K v).choose_spec.2

variable (K)

end FrobeniusDensity
