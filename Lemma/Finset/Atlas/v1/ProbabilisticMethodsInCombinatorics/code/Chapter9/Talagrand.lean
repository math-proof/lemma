import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter9.Talagrand
open MeasureTheory Real Set Metric Talagrand


namespace Talagrand

/--
[sq_sub_le_half_sq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Talagrand.lean)
-/
@[path]
lemma sq_sub_le_half_sq
  {n : ℕ}
  {t K : ℝ} :
-- imply
  t ^ 2 / 2 - K ^ 2 ≤ (t - K) ^ 2 := by
-- proof
  nlinarith [sq_nonneg (t - 2 * K)]

end Talagrand

namespace Talagrand

/--
[subgaussian_shift_center](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter9/Talagrand.lean)
-/
@[path]
lemma subgaussian_shift_center
  {n : ℕ}
  [MeasurableSpace Ω]
  {μ : Measure Ω}
  [IsProbabilityMeasure μ]
  {X : Ω → ℝ}
  {m a K : ℝ}
  {C₁ c₁ : ℝ}
  {t : ℝ}
-- given
  (hK : |m - a| ≤ K)
  (hC₁ : 1 ≤ C₁)
  (hc₁ : 0 < c₁)
  (hbound : ∀ s : ℝ, 0 ≤ s → (μ {ω | s ≤ |X ω - m|}).toReal ≤ C₁ * Real.exp (-(c₁ * s ^ 2)))
  (ht : 0 ≤ t) :
-- imply
  (μ {ω | t ≤ |X ω - a|}).toReal ≤ C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by
-- proof
  have hK_pos : 0 ≤ K := le_trans (abs_nonneg _) hK
  have hsub : {ω | t ≤ |X ω - a|} ⊆ {ω | t - K ≤ |X ω - m|} := by
    intro ω hω
    simp only [mem_setOf_eq] at *
    linarith [abs_sub_le (X ω) m a]
  by_cases htK : K ≤ t
  ·
    have hs : 0 ≤ t - K := by linarith
    have hb := hbound (t - K) hs
    have hmeas_mono : μ {ω | t ≤ |X ω - a|} ≤ μ {ω | t - K ≤ |X ω - m|} :=
      measure_mono hsub
    have h_tr : (μ {ω | t ≤ |X ω - a|}).toReal ≤ (μ {ω | t - K ≤ |X ω - m|}).toReal :=
      (ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top μ _)).mpr hmeas_mono
    calc (μ {ω | t ≤ |X ω - a|}).toReal
      ≤ C₁ * Real.exp (-(c₁ * (t - K) ^ 2)) := le_trans h_tr hb
      _ ≤ C₁ * Real.exp (-(c₁ * (t ^ 2 / 2 - K ^ 2))) := by
        gcongr; linarith [sq_sub_le_half_sq t K]
      _ = C₁ * Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) := by
        congr 1; ring_nf
      _ = C₁ * (Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2))) := by
        rw [Real.exp_add]
      _ = C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) := by ring
  ·
    simp only [not_le] at htK
    have hprob_le_one : (μ {ω | t ≤ |X ω - a|}).toReal ≤ 1 := by
      have hle : μ {ω | t ≤ |X ω - a|} ≤ 1 := by
        calc μ {ω | t ≤ |X ω - a|} ≤ μ Set.univ := measure_mono (subset_univ _)
          _ = 1 := measure_univ
      exact ENNReal.toReal_le_of_le_ofReal one_pos.le (by rwa [ENNReal.ofReal_one])
    suffices h : (1 : ℝ) ≤ C₁ * Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) from
      le_trans hprob_le_one h
    have htK2 : t ^ 2 < K ^ 2 := by nlinarith
    have h3 : (0 : ℝ) ≤ c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2)) := by nlinarith
    have h4 : (1 : ℝ) ≤ Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) :=
      Real.one_le_exp h3
    have h5 : Real.exp (c₁ * K ^ 2 + (-(c₁ / 2 * t ^ 2))) =
      Real.exp (c₁ * K ^ 2) * Real.exp (-(c₁ / 2 * t ^ 2)) :=
      Real.exp_add _ _
    nlinarith [Real.exp_pos (c₁ * K ^ 2), Real.exp_pos (-(c₁ / 2 * t ^ 2))]
/-- The distance function $x \mapsto \operatorname{dist}(x, V)$ to a linear subspace $V$
is convex and $1$-Lipschitz. -/

end Talagrand


-- created on 2026-10-23
