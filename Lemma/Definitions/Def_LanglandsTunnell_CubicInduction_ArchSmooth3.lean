import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Lemma.Definitions.Def_AutomorphicForm_SmoothingKernel
import Mathlib.Analysis.Calculus.ContDiff.Defs

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

namespace WhittakerBlock

def archRealMat3 (e : Fin 3 → Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) (AdeleRing (𝓞 ℚ) ℚ) :=
  AutomorphicForm.archMatrixInclN (Fin 3) ℚ (Matrix.of fun i j => AutomorphicForm.StandardKernel.ofReal (e i j))

open scoped Classical in

def archRealLift3 (e : Fin 3 → Fin 3 → ℝ) : AdelicGL 3 (𝓞 ℚ) ℚ :=
  if h : IsUnit (archRealMat3 e) then h.unit else 1

def IsArchSmooth3 (φ : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) : Prop :=
  ∀ g : AdelicGL 3 (𝓞 ℚ) ℚ,
    ContDiffOn ℝ (⊤ : ℕ∞) (fun e : Fin 3 → Fin 3 → ℝ => φ (g * archRealLift3 e)) {e | (Matrix.of e).det ≠ 0}

end WhittakerBlock

end
