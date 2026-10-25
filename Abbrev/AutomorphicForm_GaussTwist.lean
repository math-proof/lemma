import Structure.HeckeCharacter_FiniteOrder
import Structure.NumberField_AdelicLevel
import Def.AutomorphicForm_ConstantTerm

set_option autoImplicit false
set_option maxSynthPendingDepth 3

noncomputable section

open NumberField IsDedekindDomain NumberField.AdelicLevel

namespace AutomorphicForm.GaussTwist

section LocalRing

variable (A : Type*) [CommRing A] [IsLocalRing A]

end LocalRing

section Local

variable {R : Type*} (K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

end Local

section Adelic

variable {R K : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

end Adelic

section Gauss

variable (F : Type) [Field F] [NumberField F]

open scoped Classical

abbrev LocalGaussFactor (𝔣 : Ideal (𝓞 F)) (𝔭 : HeightOneSpectrum (𝓞 F)) : Type :=
  ((𝔭.adicCompletionIntegers F) ⧸
    (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers F))
      ^ (HeckeCharacter.idealMultiplicity F 𝔭 𝔣))ˣ

end Gauss

end AutomorphicForm.GaussTwist
