import Mathlib
import Lemma.Definitions.Def_GroupCohomology_RepPi
import Lemma.Definitions.Def_NumberField_PlaceAbove
import Lemma.Definitions.Def_NumberField_PlaceDecompositionAction

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

noncomputable def integerUnitsToUnits (v : HeightOneSpectrum (𝓞 E)) : localIntegerUnits E K v ⟶ localUnits E K v :=
  Rep.ofHom ⟨(Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom).toAdditive.toIntLinearMap,
    fun _ => rfl⟩

set_option synthInstance.maxHeartbeats 200000 in
theorem integerUnitsToUnits_hom_apply (v : HeightOneSpectrum (𝓞 E)) (u : ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K)ˣ) :
    Additive.toMul ((integerUnitsToUnits E K v).hom (Additive.ofMul u))
      = Units.map ((NumberField.PlaceAbove.above E K v).adicCompletionIntegers K).subtype.toMonoidHom u := rfl

end local_modules

abbrev Index (S : Finset (HeightOneSpectrum (𝓞 E))) : Type := {v // v ∈ S} ⊕ {v // v ∉ S}

noncomputable def fibre (S : Finset (HeightOneSpectrum (𝓞 E))) : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (fun v => Rep.coind (D E K v.1).subtype (localUnits E K v.1))
    (fun v => Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1))

@[simp] theorem fibre_inl (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∈ S}) :
    fibre E K S (Sum.inl v) = Rep.coind (D E K v.1).subtype (localUnits E K v.1) := rfl

@[simp] theorem fibre_inr (S : Finset (HeightOneSpectrum (𝓞 E))) (v : {v // v ∉ S}) :
    fibre E K S (Sum.inr v) = Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1) := rfl

noncomputable abbrev obj (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  GroupCohomology.RepPi.obj (fibre E K S)

end NumberField.FiniteSIdele
