module

public import Mathlib
public import Theorem.Rep.RepPi
public import Def.NumberField_PlaceAbove
public import Instance.NumberField_PlaceDecompositionAction

@[expose] public section

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

end local_modules

abbrev Index (S : Finset (HeightOneSpectrum (𝓞 E))) : Type := {v // v ∈ S} ⊕ {v // v ∉ S}

noncomputable abbrev fibre (S : Finset (HeightOneSpectrum (𝓞 E))) : Index E S → Rep ℤ (K ≃ₐ[E] K) :=
  Sum.elim (fun v => Rep.coind (D E K v.1).subtype (localUnits E K v.1))
    (fun v => Rep.coind (D E K v.1).subtype (localIntegerUnits E K v.1))

noncomputable abbrev obj (S : Finset (HeightOneSpectrum (𝓞 E))) : Rep ℤ (K ≃ₐ[E] K) :=
  Rep.RepPi.obj (fibre E K S)

end NumberField.FiniteSIdele