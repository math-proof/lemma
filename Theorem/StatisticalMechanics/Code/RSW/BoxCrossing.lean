/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/RSW/BoxCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.RSW.Strip.Part2
import Theorem.StatisticalMechanics.Code.RSW.SelfDuality.Part2
import Theorem.StatisticalMechanics.Code.Universality.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
open Set MeasureTheory
open scoped ENNReal NNReal


namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice

open StatMech.RSW.Box

open StatMech.RSW.Strip

open StatMech.Universality


theorem sqrt_trick_real {m s : ℝ} (hm1 : m ≤ 1)
    (h : (1 - m) ^ 2 ≤ 1 - s) : 1 - Real.sqrt (1 - s) ≤ m := by
  have h1m : (0 : ℝ) ≤ 1 - m := by linarith
  have hsqrt : Real.sqrt ((1 - m) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq h1m] at hsqrt
  linarith


theorem complFKG_union_bound {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] {A B : Set (ConfigSpace E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    μ.real Aᶜ * μ.real Bᶜ ≤ 1 - μ.real (A ∪ B) := by
  have hcomplU : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hA.union hB), probReal_univ]
  rwa [hcomplU] at hFKGc


theorem sqrt_trick {E : Type*} (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    {A B : Set (ConfigSpace E)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hm : μ.real A = μ.real B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
  set m := μ.real A with hmdef
  have hcomplA : μ.real Aᶜ = 1 - m := by rw [measureReal_compl hA, probReal_univ]
  have hcomplB : μ.real Bᶜ = 1 - m := by rw [measureReal_compl hB, probReal_univ, ← hm]
  have hbound := complFKG_union_bound μ hA hB hFKGc
  rw [hcomplA, hcomplB] at hbound
  have hkey : (1 - m) ^ 2 ≤ 1 - μ.real (A ∪ B) := by nlinarith [hbound]
  exact sqrt_trick_real (by rw [hmdef]; exact measureReal_le_one) hkey


end BoxCrossing
end RSW
end StatMech
