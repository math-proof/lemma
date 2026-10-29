/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Inequalities.BK.Part4
import Theorem.StatisticalMechanics.Code.Inequalities.DisjointOccurrence.Part3
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.Foundations.ProductMeasure.Part2
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace


variable {E : Type*}


lemma OccursOn.mono_config {A : Set (ConfigSpace E)} (hA : IsIncreasing A) {K : Set E}
    {ω ω' : ConfigSpace E} (h : ω ≤ ω') (hocc : OccursOn A K ω) :
    OccursOn A K ω' := by
  classical
  intro τ hτ
  set σ : ConfigSpace E := fun e => if e ∈ K then ω e else τ e with hσ
  have hσA : σ ∈ A := by
    apply hocc
    intro e he
    simp only [hσ, if_pos he]
  apply hA _ hσA
  intro e
  by_cases he : e ∈ K
  · simp only [hσ, if_pos he]; rw [hτ e he]; exact h e
  · simp only [hσ, if_neg he]; exact le_refl _


lemma disjointOccurrence_isIncreasing {A B : Set (ConfigSpace E)}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    IsIncreasing (disjointOccurrence A B) := by
  intro ω ω' hωω' hω
  obtain ⟨K, L, hKL, hAK, hBL⟩ := hω
  exact ⟨K, L, hKL, OccursOn.mono_config hA hωω' hAK, OccursOn.mono_config hB hωω' hBL⟩


lemma bk_triple [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1)
    {P Q R : Set (ConfigSpace E)} (hP : IsIncreasing P) (hQ : IsIncreasing Q)
    (hR : IsIncreasing R) :
    (bernoulliProductMeasure (E := E) p hp).real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ (bernoulliProductMeasure (E := E) p hp).real P
        * (bernoulliProductMeasure (E := E) p hp).real Q
        * (bernoulliProductMeasure (E := E) p hp).real R := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  have hQR : IsIncreasing (disjointOccurrence Q R) := disjointOccurrence_isIncreasing hQ hR
  calc μ.real (disjointOccurrence P (disjointOccurrence Q R))
      ≤ μ.real P * μ.real (disjointOccurrence Q R) := bk_inequality hp hP hQR
    _ ≤ μ.real P * (μ.real Q * μ.real R) :=
        mul_le_mul_of_nonneg_left (bk_inequality hp hQ hR) measureReal_nonneg
    _ = μ.real P * μ.real Q * μ.real R := by ring


theorem bk_criterion {ι : Type*} [Fintype E] [DecidableEq E] {p : NNReal} (hp : p ≤ 1)
    (s : Finset ι) (P Q R : ι → Set (ConfigSpace E))
    (hP : ∀ i ∈ s, IsIncreasing (P i)) (hQ : ∀ i ∈ s, IsIncreasing (Q i))
    (hR : ∀ i ∈ s, IsIncreasing (R i))
    {C : Set (ConfigSpace E)}
    (hC : C ⊆ ⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :
    (bernoulliProductMeasure (E := E) p hp).real C
      ≤ ∑ i ∈ s, (bernoulliProductMeasure (E := E) p hp).real (P i)
          * (bernoulliProductMeasure (E := E) p hp).real (Q i)
          * (bernoulliProductMeasure (E := E) p hp).real (R i) := by
  set μ := bernoulliProductMeasure (E := E) p hp with hμ
  calc μ.real C
      ≤ μ.real (⋃ i ∈ s, disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_mono hC (measure_ne_top _ _)
    _ ≤ ∑ i ∈ s, μ.real (disjointOccurrence (P i) (disjointOccurrence (Q i) (R i))) :=
        measureReal_biUnion_finset_le s _
    _ ≤ ∑ i ∈ s, μ.real (P i) * μ.real (Q i) * μ.real (R i) :=
        Finset.sum_le_sum (fun i hi => bk_triple hp (hP i hi) (hQ i hi) (hR i hi))


end Sharpness
end StatMech
