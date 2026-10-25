import Lemma.NumberField.AdelicLevel

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def weyl : GL (Fin 2) (AdeleRing R K) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

variable (N : Ideal R)

def principalLevel : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  levelOne R K N ⊓ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom

end NumberField.AdelicLevel

end
