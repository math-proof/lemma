import Mathlib
import Lemma.GroupCohomology.RepPi
import Lemma.NumberField.PlaceAbove
import Lemma.NumberField.PlaceDecompositionAction
import Abbrev.NumberField_FiniteSIdeleModule
import Def.NumberField_FiniteSIdeleModule

set_option autoImplicit false

open IsDedekindDomain NumberField CategoryTheory
open scoped NumberField.PlaceDecomp

namespace NumberField.FiniteSIdele

variable (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K]


section local_modules


set_option synthInstance.maxHeartbeats 200000 in
theorem integerUnitsToUnits_hom_apply (v : HeightOneSpectrum (𝓞 E)) (u : ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    Additive.toMul ((integerUnitsToUnits E K v).hom (Additive.ofMul u))
      = Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom u := rfl

end local_modules


@[simp] theorem fibre_inl (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∈ S}) :
    fibre E K S (Sum.inl v) = Rep.coind (D E K v.1).subtype (localUnits E K v.1) := rfl

@[simp] theorem fibre_inr (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∉ S}) :
    fibre E K S (Sum.inr v) = Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1) := rfl

end NumberField.FiniteSIdele
