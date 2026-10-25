import Def.AutomorphicForm_AdelicLsXi

noncomputable section

namespace AutomorphicForm

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def residualSpan (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) :=
  Submodule.span ℂ
    {φ | ∃ χ : (AdeleRing R K)ˣ →* ℂˣ, SquaresToXi R K Z ξ χ ∧ φ = chiDet R K χ}

end AutomorphicForm

end
