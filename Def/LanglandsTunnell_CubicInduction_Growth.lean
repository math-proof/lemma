import Lemma.LanglandsTunnell.CubicInduction_Carrier
import Def.AutomorphicForm_TruncationOperator

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Gauge

variable (F : Type) [Field F] [NumberField F]

def archPlaceComponent3 (w : InfinitePlace F) : AdelicGL 3 (𝓞 F) F →* GL (Fin 3) w.Completion :=
  (Matrix.GeneralLinearGroup.map (AdelicLevel.archEval F w)).comp (archComponent3 (𝓞 F) F)

variable {F}

def matrixSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    (‖(k : Matrix (Fin 3) (Fin 3) L) i j‖ + ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) i j‖)


def matrixSupSize {L : Type*} [NormedField L] (k : GL (Fin 3) L) : NNReal :=
  Finset.univ.sup fun ij : Fin 3 × Fin 3 =>
    max ‖(k : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊
      ‖((k⁻¹ : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) ij.1 ij.2‖₊

variable (F)

def archGauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  1 + ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g)

def finGauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  ∏ᶠ v : HeightOneSpectrum (𝓞 F), ((matrixSupSize (componentAt3 (𝓞 F) F v g) : NNReal) : ℝ)

def gauge3 (g : AdelicGL 3 (𝓞 F) F) : ℝ :=
  max 1 (archGauge3 F g * finGauge3 F g)

end Gauge

section Growth

variable (F : Type) [Field F] [NumberField F]

def IsModerateGrowth3 (Φ : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  AutomorphicForm.IsSlowlyIncreasingOn Set.univ (gauge3 F) Φ

end Growth

end LanglandsTunnell.CubicInduction

end
