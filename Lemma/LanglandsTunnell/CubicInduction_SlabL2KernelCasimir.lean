import Lemma.LanglandsTunnell.CubicInduction_SlabL2Cusp
import Def.LanglandsTunnell_CubicInduction_ArchCentre3
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Def.LanglandsTunnell_CubicInduction_SlabL2KernelCasimir

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.SlabL2


theorem kernelLeftDeriv_apply (i j : Fin 3) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (m : Fin 3 → Fin 3 → ℝ) :
    kernelLeftDeriv i j β m = -(fderiv ℝ β m (fun a b => if a = i then m j b else 0)) := rfl

theorem archChart_apply (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) (m : Fin 3 → Fin 3 → ℝ) :
    archChart F x m = F (x * WhittakerBlock.archRealLift3 m) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end
