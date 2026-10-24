import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_SlabL2Cusp
import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_ArchCentre3
import Mathlib.Analysis.Calculus.FDeriv.Basic

set_option autoImplicit false

noncomputable section

open IsDedekindDomain NumberField AutomorphicForm

namespace LanglandsTunnell.CubicInduction.SlabL2

def kernelEnt (h : GL (Fin 3) (InfiniteAdeleRing ℚ)) : Fin 3 → Fin 3 → ℝ :=
  fun a b => AutomorphicForm.StandardKernel.realCoord ((h : Matrix (Fin 3) (Fin 3) (InfiniteAdeleRing ℚ)) a b)

def kernelLeftDeriv (i j : Fin 3) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => -(fderiv ℝ β m (fun a b => if a = i then m j b else 0))

def kernelCasimir1 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, kernelLeftDeriv i i β m

def kernelCasimir2 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, kernelLeftDeriv i j (kernelLeftDeriv j i β) m

def kernelCasimir3 (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, kernelLeftDeriv i j (kernelLeftDeriv j k (kernelLeftDeriv k i β)) m

def kernelCasimir3T (β : (Fin 3 → Fin 3 → ℝ) → ℂ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => ∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, kernelLeftDeriv k i (kernelLeftDeriv j k (kernelLeftDeriv i j β)) m

def archChart (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) : (Fin 3 → Fin 3 → ℝ) → ℂ :=
  fun m => F (x * WhittakerBlock.archRealLift3 m)

theorem kernelLeftDeriv_apply (i j : Fin 3) (β : (Fin 3 → Fin 3 → ℝ) → ℂ) (m : Fin 3 → Fin 3 → ℝ) :
    kernelLeftDeriv i j β m = -(fderiv ℝ β m (fun a b => if a = i then m j b else 0)) := rfl

theorem archChart_apply (F : AdelicGL 3 (𝓞 ℚ) ℚ → ℂ) (x : AdelicGL 3 (𝓞 ℚ) ℚ) (m : Fin 3 → Fin 3 → ℝ) :
    archChart F x m = F (x * WhittakerBlock.archRealLift3 m) := rfl

end LanglandsTunnell.CubicInduction.SlabL2

end
