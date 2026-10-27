import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.KestenUncond
open MeasureTheory Set Filter StatMech StatMech.TwoDim


/--
[theta_half_eq_zero_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean)
-/
@[path]
private lemma theta_half_eq_zero_uncond_eq
-- given
  (h12 : (1 / 2 : ℝ≥0) ≤ 1)
  (cross : ℝ≥0 → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  theta 2 (1 / 2) h12 = 0 := by
-- proof
  apply StatMech.TwoDim.theta_half_eq_zero_uncond h12 cross hdualHalf hpercToOne

/--
[half_mem_subcriticalSet_uncond](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean)
-/
@[path]
private lemma half_mem_subcriticalSet_uncond_eq
-- given
  (h12 : (1 / 2 : ℝ≥0) ≤ 1)
  (cross : ℝ≥0 → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  (1 / 2 : ℝ≥0) ∈ subcriticalSet 2 := by
-- proof
  apply StatMech.TwoDim.half_mem_subcriticalSet_uncond h12 cross hdualHalf hpercToOne

/--
[kesten_half_le_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean)
-/
@[path]
private lemma kesten_half_le_pc_eq
-- given
  (h12 : (1 / 2 : ℝ≥0) ≤ 1)
  (cross : ℝ≥0 → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  (1 / 2 : ℝ≥0) ≤ pc 2 := by
-- proof
  apply StatMech.TwoDim.kesten_half_le_pc h12 cross hdualHalf hpercToOne

/--
[kesten_pc_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean)
-/
@[path]
private lemma kesten_pc_le_half_eq
-- given
  (cross : ℝ≥0 → ℕ → ℝ)
  (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1, (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) → Tendsto (cross p) atTop (𝓝 0)) :
-- imply
  pc 2 ≤ (1 / 2 : ℝ≥0) := by
-- proof
  apply StatMech.TwoDim.kesten_pc_le_half cross hmono hdualHalf hdecayToZero

/--
[kesten_pc_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/KestenUncond.lean)
-/
@[path]
private lemma kesten_pc_eq_half_eq
-- given
  (h12 : (1 / 2 : ℝ≥0) ≤ 1)
  (cross : ℝ≥0 → ℕ → ℝ)
  (hmono : ∀ n, ∀ p q : ℝ≥0, p ≤ q → cross p n ≤ cross q n)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1))
  (hdecayToZero : ∀ p : ℝ≥0, ∀ hp : p ≤ 1, (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) → Tendsto (cross p) atTop (𝓝 0)) :
-- imply
  pc 2 = (1 / 2 : ℝ≥0) := by
-- proof
  apply StatMech.TwoDim.kesten_pc_eq_half h12 cross hmono hdualHalf hpercToOne hdecayToZero


-- created on 2026-10-23
