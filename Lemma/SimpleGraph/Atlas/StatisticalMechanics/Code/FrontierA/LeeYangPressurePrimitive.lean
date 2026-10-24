import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangPressurePrimitive
open Complex Filter Metric Set Topology StatMech StatMech.FrontierA


/--
[leeYangRightCayley_mem_ball](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangRightCayley_mem_ball_eq
  {z : ℂ}
-- given
  (hz : 0 < z.re) :
-- imply
  leeYangRightCayley z ∈ ball 0 1 := by
-- proof
  apply StatMech.FrontierA.leeYangRightCayley_mem_ball hz

/--
[leeYangRightCayleyInv_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangRightCayleyInv_mem_eq
  {w : ℂ}
-- given
  (hw : w ∈ ball 0 1) :
-- imply
  0 < (leeYangRightCayleyInv w).re := by
-- proof
  apply StatMech.FrontierA.leeYangRightCayleyInv_mem hw

/--
[leeYangRightCayleyInv_cayley](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangRightCayleyInv_cayley_eq
  {z : ℂ}
-- given
  (hz : z ≠ -1) :
-- imply
  leeYangRightCayleyInv (leeYangRightCayley z) = z := by
-- proof
  apply StatMech.FrontierA.leeYangRightCayleyInv_cayley z hz

/--
[hasDerivAt_leeYangRightCayley](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma hasDerivAt_leeYangRightCayley_eq
  {z : ℂ}
-- given
  (hz : 0 < z.re) :
-- imply
  HasDerivAt leeYangRightCayley (2 / (z + 1) ^ 2) z := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_leeYangRightCayley z hz

/--
[hasDerivAt_leeYangRightCayleyInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma hasDerivAt_leeYangRightCayleyInv_eq
  {w : ℂ}
-- given
  (hw : w ∈ ball 0 1) :
-- imply
  HasDerivAt leeYangRightCayleyInv (2 / (1 - w) ^ 2) w := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_leeYangRightCayleyInv w hw

/--
[leeYangCayleyPulledDerivative_differentiableOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangCayleyPulledDerivative_differentiableOn_eq
  {g : ℂ → ℂ}
-- given
  (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re}) :
-- imply
  DifferentiableOn ℂ (leeYangCayleyPulledDerivative g) (ball 0 1) := by
-- proof
  apply StatMech.FrontierA.leeYangCayleyPulledDerivative_differentiableOn g hg

/--
[rightHalfPlane_normalizedPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma rightHalfPlane_normalizedPrimitive_eq
  {g : ℂ → ℂ}
  {p₀ : ℂ}
-- given
  (hg : DifferentiableOn ℂ g {z : ℂ | 0 < z.re})
  (h₀ : ℝ)
  (hh₀ : 0 < h₀) :
-- imply
  ∃ P : ℂ → ℂ, P (h₀ : ℂ) = p₀ ∧ HasDerivAt P (g (h₀ : ℂ)) (h₀ : ℂ) ∧ ∀ z, z ∈ {z : ℂ | 0 < z.re} → HasDerivAt P (g z) z := by
-- proof
  apply StatMech.FrontierA.rightHalfPlane_normalizedPrimitive g hg h₀ hh₀ p₀

/--
[leftHalfPlane_normalizedPrimitive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leftHalfPlane_normalizedPrimitive_eq
  {g : ℂ → ℂ}
  {p₀ : ℂ}
-- given
  (hg : DifferentiableOn ℂ g {z : ℂ | z.re < 0})
  (h₀ : ℝ)
  (hh₀ : h₀ < 0) :
-- imply
  ∃ P : ℂ → ℂ, P (h₀ : ℂ) = p₀ ∧ HasDerivAt P (g (h₀ : ℂ)) (h₀ : ℂ) ∧ ∀ z, z ∈ {z : ℂ | z.re < 0} → HasDerivAt P (g z) z := by
-- proof
  apply StatMech.FrontierA.leftHalfPlane_normalizedPrimitive g hg h₀ hh₀ p₀

/--
[leeYangBox_holomorphicPressure_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangBox_holomorphicPressure_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (h₀ : ℝ)
  (hh₀ : 0 < h₀) :
-- imply
  ∃ (P g : ℂ → ℂ), P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧ TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ P {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ Set.EqOn (deriv P) g {z : ℂ | 0 < z.re} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | 0 < z.re} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_holomorphicPressure_rightHalfPlane d hd hbeta h₀ hh₀

/--
[leeYangBox_holomorphicPressure_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressurePrimitive.lean)
-/
@[path]
private lemma leeYangBox_holomorphicPressure_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (h₀ : ℝ)
  (hh₀ : h₀ < 0) :
-- imply
  ∃ (P g : ℂ → ℂ), P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧ TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ P {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ Set.EqOn (deriv P) g {z : ℂ | z.re < 0} ∧ TendstoLocallyUniformlyOn (deriv ∘ fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) (deriv g) atTop {z : ℂ | z.re < 0} := by
-- proof
  apply StatMech.FrontierA.leeYangBox_holomorphicPressure_leftHalfPlane d hd hbeta h₀ hh₀


-- created on 2026-10-23
