/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FK.TwoPointInfinite
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


theorem le_ivTwoPointSup (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : (μ n) A ≤ ivTwoPointSup μ A :=
  le_ciSup (bddAbove_range_apply μ A) n


theorem ivTwoPointInf_le (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) (n : ℕ) : ivTwoPointInf μ A ≤ (μ n) A :=
  ciInf_le (OrderBot.bddBelow _) n


theorem ivTwoPointSup_pos (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {n : ℕ} (hn : 0 < (μ n) A) : 0 < ivTwoPointSup μ A :=
  lt_of_lt_of_le hn (le_ivTwoPointSup μ A n)


theorem ivTwoPointInf_pos_of_uniform (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (A : Set (ConfigSpace E)) {c : NNReal} (hc : 0 < c) (hbound : ∀ n, c ≤ (μ n) A) :
    0 < ivTwoPointInf μ A :=
  lt_of_lt_of_le hc (le_ciInf hbound)


theorem ivTwoPointSup_isLimit (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (hchain : ∀ n, (μ n : Measure (ConfigSpace E)) ≼ (μ (n + 1) : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointSup μ A)) :=
  tendsto_NNReal_of_monotone_isIncreasing hchain hAclopen hAinc


theorem ivTwoPointInf_isLimit (μ : ℕ → ProbabilityMeasure (ConfigSpace E))
    (hchain : ∀ n, (μ (n + 1) : Measure (ConfigSpace E)) ≼ (μ n : Measure (ConfigSpace E)))
    {A : Set (ConfigSpace E)} (hAclopen : IsClopen A) (hAinc : IsIncreasing A) :
    Tendsto (fun n => (μ n) A) atTop (𝓝 (ivTwoPointInf μ A)) := by
  have hAmeas := IsClopen.measurableSet_configSpace hAclopen
  have hanti : Antitone (fun n => (μ n) A) := by
    apply antitone_nat_of_succ_le
    intro n
    have hreal : (μ (n + 1) : Measure (ConfigSpace E)).real A
        ≤ (μ n : Measure (ConfigSpace E)).real A := hchain n A hAmeas hAinc
    rw [← ProbabilityMeasure.coe_apply_eq_real, ← ProbabilityMeasure.coe_apply_eq_real] at hreal
    exact_mod_cast hreal
  exact tendsto_atTop_ciInf hanti (OrderBot.bddBelow _)


end FK
end StatMech
