import Lemma.Definitions.Def_AutomorphicForm_AdelicLsXi

noncomputable section

namespace AutomorphicForm

open NumberField

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def residualSpan (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ) :
    Submodule ℂ (AdelicGL2 R K → ℂ) :=
  Submodule.span ℂ
    {φ | ∃ χ : (AdeleRing R K)ˣ →* ℂˣ, SquaresToXi R K Z ξ χ ∧ φ = chiDet R K χ}

variable {R K}

theorem chiDet_mem_residualSpan {Z : Subgroup (AdeleRing R K)ˣ} {ξ : Z →* ℂˣ}
    {χ : (AdeleRing R K)ˣ →* ℂˣ} (h : SquaresToXi R K Z ξ χ) :
    chiDet R K χ ∈ residualSpan R K Z ξ :=
  Submodule.subset_span ⟨χ, h, rfl⟩

theorem residualSpan_eq_bot_of_forall_not {Z : Subgroup (AdeleRing R K)ˣ} {ξ : Z →* ℂˣ}
    (h : ∀ χ : (AdeleRing R K)ˣ →* ℂˣ, ¬ SquaresToXi R K Z ξ χ) :
    residualSpan R K Z ξ = ⊥ := by
  refine Submodule.span_eq_bot.mpr ?_
  rintro φ ⟨χ, hχ, -⟩
  exact absurd hχ (h χ)

end AutomorphicForm
