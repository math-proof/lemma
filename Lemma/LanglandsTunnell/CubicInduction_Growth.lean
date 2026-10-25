import Lemma.LanglandsTunnell.CubicInduction_Carrier
import Lemma.AutomorphicForm.TruncationOperator
import Def.LanglandsTunnell_CubicInduction_Growth

set_option autoImplicit false

open IsDedekindDomain NumberField Matrix

noncomputable section

namespace LanglandsTunnell.CubicInduction

section Gauge

variable (F : Type) [Field F] [NumberField F]


variable {F}


theorem matrixSize_nonneg {L : Type*} [NormedField L] (k : GL (Fin 3) L) : 0 ≤ matrixSize k :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => add_nonneg (norm_nonneg _) (norm_nonneg _)


variable (F)


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


theorem isModerateGrowth3_zero : IsModerateGrowth3 F (fun _ => (0 : ℂ)) :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded (C := 0) fun _ _ => by simp

theorem isModerateGrowth3_of_bounded {Φ : AdelicGL 3 (𝓞 F) F → ℂ} {C : ℝ} (hC : ∀ g, ‖Φ g‖ ≤ C) :
    IsModerateGrowth3 F Φ :=
  AutomorphicForm.isSlowlyIncreasingOn_of_bounded fun g _ => hC g

end Growth

end LanglandsTunnell.CubicInduction

end
