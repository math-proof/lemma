import Lemma.NumberField.AdelicLevel
import Def.NumberField_PrincipalLevel

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


variable (N : Ideal R)


theorem principalLevel_le_levelOne : principalLevel R K N ≤ levelOne R K N := inf_le_left

theorem mem_principalLevel_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ principalLevel R K N ↔
      g ∈ levelOne R K N ∧ g ∈ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom :=
  Iff.rfl

end NumberField.AdelicLevel

end
