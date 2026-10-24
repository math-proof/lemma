import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.LeeYangPressureIdentification
open Complex Filter Set Topology StatMech StatMech.FrontierA


/--
[leeYangPressurePrimitive_eq_real_rightHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressureIdentification.lean)
-/
@[path]
private lemma leeYangPressurePrimitive_eq_real_rightHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {P g : ℂ → ℂ}
-- given
  (hd : 1 ≤ d)
  (h₀ : ℝ)
  (hh₀ : 0 < h₀)
  (hanchor : P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ))
  (hlimit : TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | 0 < z.re})
  (hPdiff : DifferentiableOn ℂ P {z : ℂ | 0 < z.re})
  (hPderiv : Set.EqOn (deriv P) g {z : ℂ | 0 < z.re}) :
-- imply
  ∀ h : ℝ, 0 < h → P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangPressurePrimitive_eq_real_rightHalfPlane d hd beta P g h₀ hh₀ hanchor hlimit hPdiff hPderiv

/--
[leeYangPressurePrimitive_eq_real_leftHalfPlane](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressureIdentification.lean)
-/
@[path]
private lemma leeYangPressurePrimitive_eq_real_leftHalfPlane_eq
  {d : ℕ}
  {beta : ℝ}
  {P g : ℂ → ℂ}
-- given
  (hd : 1 ≤ d)
  (h₀ : ℝ)
  (hh₀ : h₀ < 0)
  (hanchor : P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ))
  (hlimit : TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | z.re < 0})
  (hPdiff : DifferentiableOn ℂ P {z : ℂ | z.re < 0})
  (hPderiv : Set.EqOn (deriv P) g {z : ℂ | z.re < 0}) :
-- imply
  ∀ h : ℝ, h < 0 → P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ) := by
-- proof
  apply StatMech.FrontierA.leeYangPressurePrimitive_eq_real_leftHalfPlane d hd beta P g h₀ hh₀ hanchor hlimit hPdiff hPderiv

/--
[leeYangBox_holomorphicPressure_rightHalfPlane_identified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressureIdentification.lean)
-/
@[path]
private lemma leeYangBox_holomorphicPressure_rightHalfPlane_identified_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (h₀ : ℝ)
  (hh₀ : 0 < h₀) :
-- imply
  ∃ (P g : ℂ → ℂ), P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧ TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ P {z : ℂ | 0 < z.re} ∧ DifferentiableOn ℂ g {z : ℂ | 0 < z.re} ∧ Set.EqOn (deriv P) g {z : ℂ | 0 < z.re} ∧ (∀ h : ℝ, 0 < h → P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ)) := by
-- proof
  apply StatMech.FrontierA.leeYangBox_holomorphicPressure_rightHalfPlane_identified d hd hbeta h₀ hh₀

/--
[leeYangBox_holomorphicPressure_leftHalfPlane_identified](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/LeeYangPressureIdentification.lean)
-/
@[path]
private lemma leeYangBox_holomorphicPressure_leftHalfPlane_identified_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hd : 1 ≤ d)
  (hbeta : 0 < beta)
  (h₀ : ℝ)
  (hh₀ : h₀ < 0) :
-- imply
  ∃ (P g : ℂ → ℂ), P (h₀ : ℂ) = (isingBoxPressureLimit d hd beta h₀ : ℂ) ∧ TendstoLocallyUniformlyOn (fun n => leeYangNormalizedFieldLogDerivative (boxGraph d n) beta) g atTop {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ P {z : ℂ | z.re < 0} ∧ DifferentiableOn ℂ g {z : ℂ | z.re < 0} ∧ Set.EqOn (deriv P) g {z : ℂ | z.re < 0} ∧ (∀ h : ℝ, h < 0 → P (h : ℂ) = (isingBoxPressureLimit d hd beta h : ℂ)) := by
-- proof
  apply StatMech.FrontierA.leeYangBox_holomorphicPressure_leftHalfPlane_identified d hd hbeta h₀ hh₀


-- created on 2026-10-23
