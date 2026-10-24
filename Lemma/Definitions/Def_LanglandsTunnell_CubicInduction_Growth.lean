import Lemma.Definitions.Def_LanglandsTunnell_CubicInduction_Carrier
import Lemma.Definitions.Def_AutomorphicForm_TruncationOperator

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

theorem matrixSize_nonneg {L : Type*} [NormedField L] (k : GL (Fin 3) L) : 0 ≤ matrixSize k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)

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

theorem one_le_gauge3 (g : AdelicGL 3 (𝓞 F) F) : 1 ≤ gauge3 F g :=
  le_max_left _ _

theorem gauge3_pos (g : AdelicGL 3 (𝓞 F) F) : 0 < gauge3 F g :=
  lt_of_lt_of_le zero_lt_one (one_le_gauge3 F g)

theorem one_le_archGauge3 (g : AdelicGL 3 (𝓞 F) F) : 1 ≤ archGauge3 F g := by
  unfold archGauge3
  have h : 0 ≤ ∑ w : InfinitePlace F, matrixSize (archPlaceComponent3 F w g) :=
    Finset.sum_nonneg fun w _ => matrixSize_nonneg _
  linarith

end Gauge

section Growth

variable (F : Type) [Field F] [NumberField F]

def IsModerateGrowth3 (Φ : AdelicGL 3 (𝓞 F) F → ℂ) : Prop :=
  AutomorphicForm.IsSlowlyIncreasingOn Set.univ (gauge3 F) Φ

theorem isModerateGrowth3_zero : IsModerateGrowth3 F (fun _ => (0 : ℂ)) :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded (C := 0) fun _ _ => by simp

theorem isModerateGrowth3_of_bounded {Φ : AdelicGL 3 (𝓞 F) F → ℂ} {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C) :
    IsModerateGrowth3 F Φ :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded fun g _ => hC g

end Growth

end LanglandsTunnell.CubicInduction
