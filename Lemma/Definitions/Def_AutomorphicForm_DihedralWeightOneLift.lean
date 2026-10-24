import Lemma.Definitions.Def_LanglandsTunnell_DeltaLift

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Matrix AutomorphicForm
open scoped ModularForm MatrixGroups

namespace DihedralWeightOne

def weightOneArchLift (f : UpperHalfPlane → ℂ) (h : GL (Fin 2) ℝ) : ℂ :=
  (f ∣[(1 : ℤ)] h) UpperHalfPlane.I * ((h.det.val : ℝ) : ℂ) ^ (1 : ℤ)

def HasWeightOneDecomp (N : Ideal (𝓞 ℚ)) (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : Prop :=
  ∃ (γ : GL (Fin 2) ℚ) (h u : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)),
    u ∈ (productionPinsCompact ℚ).U N ∧ AdelicLevel.glFin (𝓞 ℚ) ℚ h = 1 ∧
    LanglandsTunnell.ratArchGL2 h ∈ GLPos (Fin 2) ℝ ∧
    g = AutomorphicForm.globalPoints (𝓞 ℚ) ℚ γ * h * u

open scoped Classical in

def weightOneLift (N : Ideal (𝓞 ℚ)) (f : UpperHalfPlane → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 ℚ) ℚ)) : ℂ :=
  if H : HasWeightOneDecomp N g then
    weightOneArchLift f (LanglandsTunnell.ratArchGL2 H.choose_spec.choose) else 0

end DihedralWeightOne

end
