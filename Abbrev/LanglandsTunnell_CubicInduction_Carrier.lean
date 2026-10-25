import Structure.AutomorphicForm_AdelicLsXi
import Def.AutomorphicForm_ConstantTerm
import Structure.NumberField_AdelicLevel

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Carrier

variable (n : ℕ) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL : Type _ := Matrix.GeneralLinearGroup (Fin n) (AdeleRing R K)

end Carrier

section Unipotent

variable {A : Type*} [CommRing A]

end Unipotent

section Iota

variable {A : Type*} [CommRing A]

abbrev MirabolicIndex : Type _ :=
  Quotient (QuotientGroup.rightRel (AutomorphicForm.unipotentGL2Hom (R := K)).range)

end Iota

section LocalCompact

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end LocalCompact

section Components

variable (ι : Type*) [Fintype ι] [DecidableEq ι]
variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

variable (v : HeightOneSpectrum R)

end Components

section Three

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

end Three

end LanglandsTunnell.CubicInduction
