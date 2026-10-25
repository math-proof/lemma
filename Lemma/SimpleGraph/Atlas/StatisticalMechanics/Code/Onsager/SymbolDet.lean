import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SymbolDet
open StatMech StatMech.Onsager


/--
[ons_symbol_det_z](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SymbolDet.lean)
-/
@[path]
private lemma ons_symbol_det_z_eq
  {x ω z₁ z₂ : ℂ}
-- given
  (hω : ω^2 = Complex.I)
  (hz₁ : z₁ ≠ 0)
  (hz₂ : z₂ ≠ 0) :
-- imply
  (ons_KWsymbolMat x ω z₁ z₂).det = (1 + x^2)^2 - x*(1 - x^2)*(z₁ + z₁⁻¹ + z₂ + z₂⁻¹) := by
-- proof
  apply StatMech.Onsager.ons_symbol_det_z x ω z₁ z₂ hω hz₁ hz₂

/--
[ons_symbol_det_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SymbolDet.lean)
-/
@[path]
private lemma ons_symbol_det_cos_eq
  {x k₁ k₂ : ℝ} :
-- imply
  (ons_KWsymbolMat (x:ℂ) (Complex.exp (Complex.I*(Real.pi/4))) (Complex.exp (Complex.I*k₁)) (Complex.exp (Complex.I*k₂))).det = ((1 + (x:ℂ)^2)^2 - 2*x*(1 - (x:ℂ)^2)*((Real.cos k₁ : ℂ) + (Real.cos k₂ : ℂ))) := by
-- proof
  apply StatMech.Onsager.ons_symbol_det_cos x k₁ k₂

/--
[ons_dispersion_cosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SymbolDet.lean)
-/
@[path]
private lemma ons_dispersion_cosh_eq
  {β c : ℝ} :
-- imply
  (1 + Real.tanh β^2)^2 - 2*Real.tanh β*(1 - Real.tanh β^2)*c = (Real.cosh (2*β)^2 - Real.sinh (2*β)*c) / Real.cosh β^4 := by
-- proof
  apply StatMech.Onsager.ons_dispersion_cosh β c


-- created on 2026-10-23
