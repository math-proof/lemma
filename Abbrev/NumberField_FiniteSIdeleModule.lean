import Mathlib
import Lemma.GroupCohomology.RepPi
import Def.NumberField_PlaceAbove
import Instance.NumberField_PlaceDecompositionAction

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]

noncomputable abbrev D (v : HeightOneSpectrum (𝓞 E)) : Subgroup (K ≃ₐ[E] K) :=
  NumberField.PlaceDecomp.decomp E K (NumberField.PlaceAbove.above E K v)

section local_modules

noncomputable abbrev localUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletion K)ˣ

noncomputable abbrev localIntegerUnits (v : HeightOneSpectrum (𝓞 E)) : Rep ℤ (D E K v) :=
  Rep.ofMulDistribMulAction (D E K v) ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ

set_option synthInstance.maxHeartbeats 200000 in


end local_modules

abbrev Index (S : Finset (HeightOneSpectrum (𝓞 E))) : Type := {v // v ∈ S} ⊕ {v // v ∉ S}


end NumberField.FiniteSIdele

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]


section local_modules


end local_modules


noncomputable abbrev obj (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  GroupCohomology.RepPi.obj (fibre E K S)

end NumberField.FiniteSIdele
