/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BernoulliGlobalFKG.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.Ergodicity
import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.Universality.BXPAspectTransfer
import Theorem.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part101
import Def.StatisticalMechanics.Code.Universality.BernoulliGlobalFKG.Part2
open MeasureTheory Set Filter
open scoped ENNReal NNReal symmDiff


namespace StatMech

namespace Universality

open StatMech.Lattice

open StatMech.Percolation

open StatMech.RSW.Box

open StatMech.RSW.Strip


theorem measurablyPositivelyAssociated_of_increasingCylinderApproximation
    {E : Type*} {μ : Measure (ConfigSpace E)} [IsFiniteMeasure μ]
    (hcyl : FiniteCylinderPositivelyAssociated μ)
    (happrox : ∀ A : Set (ConfigSpace E), MeasurableSet A → IsIncreasing A →
      HasIncreasingCylinderApproximation μ A) :
    MeasurablyPositivelyAssociated μ := by
  intro A B hAm hBm hA hB
  obtain ⟨C, hCm, hCi, hCdep, hCt⟩ := happrox A hAm hA
  obtain ⟨D, hDm, hDi, hDdep, hDt⟩ := happrox B hBm hB
  have hCprob : Tendsto (fun n => μ.real (C n)) atTop (nhds (μ.real A)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hCt
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        (hCm n).nullMeasurableSet hAm.nullMeasurableSet)
  have hDprob : Tendsto (fun n => μ.real (D n)) atTop (nhds (μ.real B)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hDt
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        (hDm n).nullMeasurableSet hBm.nullMeasurableSet)
  have hInterDiff : Tendsto
      (fun n => μ.real ((C n ∩ D n) ∆ (A ∩ B)))
      atTop (nhds 0) := by
    apply squeeze_zero (fun _ => measureReal_nonneg) _
      (by simpa using hCt.add hDt)
    intro n
    calc
      μ.real ((C n ∩ D n) ∆ (A ∩ B))
          ≤ μ.real ((C n ∆ A) ∪ (D n ∆ B)) := by
            apply measureReal_mono _ (measure_ne_top _ _)
            intro omega homega
            simp only [mem_symmDiff, mem_inter_iff, mem_union] at homega ⊢
            tauto
      _ ≤ μ.real (C n ∆ A) + μ.real (D n ∆ B) :=
        measureReal_union_le _ _
  have hInterProb : Tendsto (fun n => μ.real (C n ∩ D n)) atTop
      (nhds (μ.real (A ∩ B))) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) _ hInterDiff
    intro n
    simpa only [Real.dist_eq] using
      (abs_measureReal_sub_le_measureReal_symmDiff
        ((hCm n).inter (hDm n)).nullMeasurableSet
        (hAm.inter hBm).nullMeasurableSet)
  have hstage : ∀ n,
      μ.real (C n) * μ.real (D n) ≤ μ.real (C n ∩ D n) := by
    intro n
    obtain ⟨F, hF⟩ := hCdep n
    obtain ⟨G, hG⟩ := hDdep n
    exact hcyl (C n) (D n) (hCi n) (hDi n) F G hF hG
  exact le_of_tendsto_of_tendsto (hCprob.mul hDprob) hInterProb
    (Eventually.of_forall hstage)


theorem positivelyAssociated_of_measurablyPositivelyAssociated
    {E : Type*} {μ : Measure (ConfigSpace E)}
    (hpa : MeasurablyPositivelyAssociated μ)
    (hmeas : ∀ A : Set (ConfigSpace E), IsIncreasing A → MeasurableSet A) :
    PositivelyAssociated μ := by
  intro A B hA hB
  exact hpa A B (hmeas A hA) (hmeas B hB) hA hB


theorem bernoulli_exists_cylinder_symmDiff_lt
    {E : Type*} [Countable E]
    (p : ℝ≥0) (hp : p ≤ 1) {A : Set (ConfigSpace E)}
    (hA : MeasurableSet A) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ C ∈ measurableCylinders (fun _ : E => Bool),
      bernoulliProductMeasure (E := E) p hp (C ∆ A) < ε :=
  FK.exists_cylinder_symmDiff_lt p hp hA hε

end Universality
end StatMech
