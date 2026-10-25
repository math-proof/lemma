import Mathlib

set_option autoImplicit false

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain
open scoped nonZeroDivisors

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end IsDedekindDomain.selmerGroup

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

end IsDedekindDomain.selmerGroup

end

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

end IsDedekindDomain.selmerGroup

end

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ) [Fact (0 < n)]

abbrev Qn : Type := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

abbrev Sel : Subgroup (Qn K n) := selmerGroup (R := R) (K := K) (S := S) (n := n)

end IsDedekindDomain.selmerGroup

end
