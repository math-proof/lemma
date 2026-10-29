import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.Kesten
open MeasureTheory Set Filter StatMech StatMech.TwoDim


/--
[theta_half_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean)
-/
@[path]
private lemma theta_half_eq_zero_eq
-- given
  (h12 : (1 / 2 : NNReal) ≤ 1)
  (cross : NNReal → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  theta 2 (1 / 2) h12 = 0 := by
-- proof
  apply StatMech.TwoDim.theta_half_eq_zero h12 cross hdualHalf hpercToOne

/--
[half_mem_subcriticalSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean)
-/
@[path]
private lemma half_mem_subcriticalSet_eq
-- given
  (h12 : (1 / 2 : NNReal) ≤ 1)
  (cross : NNReal → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  (1 / 2 : NNReal) ∈ subcriticalSet 2 := by
-- proof
  apply StatMech.TwoDim.half_mem_subcriticalSet h12 cross hdualHalf hpercToOne

/--
[half_le_pc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean)
-/
@[path]
private lemma half_le_pc_eq
-- given
  (h12 : (1 / 2 : NNReal) ≤ 1)
  (cross : NNReal → ℕ → ℝ)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1)) :
-- imply
  (1 / 2 : NNReal) ≤ pc 2 := by
-- proof
  apply StatMech.TwoDim.half_le_pc h12 cross hdualHalf hpercToOne

/--
[pc_le_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean)
-/
@[path]
private lemma pc_le_half_eq
-- given
  (hsharp : tildePc 2 = pc 2)
  (cross : NNReal → ℕ → ℝ)
  (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
  (hmono : ∀ n, ∀ p q : NNReal, p ≤ q → cross p n ≤ cross q n)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hdecayToZero : ∀ p : NNReal, ∀ hp : p ≤ 1, (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) → Tendsto (cross p) atTop (𝓝 0)) :
-- imply
  pc 2 ≤ (1 / 2 : NNReal) := by
-- proof
  apply StatMech.TwoDim.pc_le_half hsharp cross hsub hmono hdualHalf hdecayToZero

/--
[pc_eq_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/Kesten.lean)
-/
@[path]
private lemma pc_eq_half_eq
-- given
  (h12 : (1 / 2 : NNReal) ≤ 1)
  (hsharp : tildePc 2 = pc 2)
  (cross : NNReal → ℕ → ℝ)
  (hsub : ∀ p ∈ tildePcSet 2, ∀ hp : p ≤ 1, ∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n))
  (hmono : ∀ n, ∀ p q : NNReal, p ≤ q → cross p n ≤ cross q n)
  (hdualHalf : ∀ n, cross (1 / 2) n = 1 / 2)
  (hpercToOne : 0 < theta 2 (1 / 2) h12 → Tendsto (cross (1 / 2)) atTop (𝓝 1))
  (hdecayToZero : ∀ p : NNReal, ∀ hp : p ≤ 1, (∃ c > 0, ∃ C > 0, ∀ n, crossProb 2 p hp n ≤ C * Real.exp (-c * n)) → Tendsto (cross p) atTop (𝓝 0)) :
-- imply
  pc 2 = (1 / 2 : NNReal) := by
-- proof
  apply StatMech.TwoDim.pc_eq_half h12 hsharp cross hsub hmono hdualHalf hpercToOne hdecayToZero


-- created on 2026-10-23
