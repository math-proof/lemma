import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.FourierGaussian
open Real MeasureTheory Complex FourierAnalysis
open scoped RealInnerProductSpace


namespace FourierAnalysis

/--
[fourier_transform_gaussian](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/FourierGaussian.lean)
-/
@[path]
lemma fourier_transform_gaussian
  [NormedAddCommGroup V]
  [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]
  {w : V} :
-- imply
  bookFourierTransform (fun v => cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2)) w = ↑((2 * π) ^ ((Module.finrank ℝ V : ℝ) / 2)) * cexp (-(1 / 2 : ℂ) * ‖w‖ ^ 2) := by
-- proof
  show ∫ v, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2) =
    ↑((2 * π) ^ ((Module.finrank ℝ V : ℝ) / 2)) * cexp (-(1 / 2 : ℂ) * ‖w‖ ^ 2)
  have hcomb : ∀ v : V, cexp (-(I : ℂ) * ↑(⟪v, w⟫)) * cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2) =
    cexp (-(1 / 2 : ℂ) * ‖v‖ ^ 2 + (-I : ℂ) * (⟪w, v⟫ : ℝ)) := fun v => by
    rw [← Complex.exp_add]; congr 1; rw [real_inner_comm v w]; push_cast; ring
  simp_rw [hcomb]
  rw [GaussianFourier.integral_cexp_neg_mul_sq_norm_add
    (show (0 : ℝ) < ((1 / 2 : ℂ)).re by norm_num) (-I : ℂ) w]
  have h_exp : (-I : ℂ) ^ 2 * ‖w‖ ^ 2 / (4 * (1 / 2 : ℂ)) = -(1 / 2 : ℂ) * ‖w‖ ^ 2 := by
    rw [neg_sq, I_sq]; ring
  rw [h_exp]
  have h_coeff : (π : ℂ) / (1 / 2 : ℂ) = ↑(2 * π) := by push_cast; ring
  rw [h_coeff]
  congr 1
  rw [show (Module.finrank ℝ V / 2 : ℂ) = ↑((Module.finrank ℝ V : ℝ) / 2) from by
    push_cast; ring]
  exact (ofReal_cpow (by positivity : (0 : ℝ) ≤ 2 * π) _).symm
end FourierAnalysis



-- created on 2026-10-23
