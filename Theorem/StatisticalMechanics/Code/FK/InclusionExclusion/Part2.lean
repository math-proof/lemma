/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InclusionExclusion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Def.StatisticalMechanics.Code.FK.InclusionExclusion.Part2
open StatMech ConfigSpace
open scoped BigOperators Pointwise


namespace StatMech

namespace FK

variable {E : Type*}


theorem signedIncreasingCombo_iff (f : ConfigSpace E → ℝ) :
    SignedIncreasingCombo f ↔
      ∃ (ι : Type) (s : Finset ι) (c : ι → ℝ) (A : ι → Set (ConfigSpace E)),
        (∀ i ∈ s, IsIncreasing (A i)) ∧
          f = ∑ i ∈ s, c i • (A i).indicator (1 : ConfigSpace E → ℝ) := by
  constructor
  · intro hf
    
    rw [SignedIncreasingCombo, Submodule.mem_span_set'] at hf
    obtain ⟨n, c, g, hsum⟩ := hf
    
    classical
    refine ⟨Fin n, Finset.univ, c,
      fun i => ((g i).2).choose, fun i _ => ((g i).2).choose_spec.1, ?_⟩
    rw [← hsum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ((g i).2).choose_spec.2]
  · rintro ⟨ι, s, c, A, hA, rfl⟩
    refine Submodule.sum_mem _ fun i hi => ?_
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨A i, hA i hi, rfl⟩)


lemma span_mul_mem {f g : ConfigSpace E → ℝ}
    (hf : f ∈ Submodule.span ℝ (incrIndicators E))
    (hg : g ∈ Submodule.span ℝ (incrIndicators E)) :
    f * g ∈ Submodule.span ℝ (incrIndicators E) := by
  have hmul : incrIndicators E * incrIndicators E ⊆ incrIndicators E := by
    rintro _ ⟨a, ha, b, hb, rfl⟩
    obtain ⟨A, hA, rfl⟩ := ha
    obtain ⟨B, hB, rfl⟩ := hb
    exact ⟨A ∩ B, IsUpperSet.inter hA hB, Set.inter_indicator_one.symm⟩
  have h : f * g ∈ Submodule.span ℝ (incrIndicators E) * Submodule.span ℝ (incrIndicators E) :=
    Submodule.mul_mem_mul hf hg
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hmul h


lemma prod_mem_span {ι : Type*} (s : Finset ι) (f : ι → ConfigSpace E → ℝ)
    (hf : ∀ i ∈ s, f i ∈ Submodule.span ℝ (incrIndicators E)) :
    (∏ i ∈ s, f i) ∈ Submodule.span ℝ (incrIndicators E) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp only [Finset.prod_empty]
    exact Submodule.subset_span one_mem_incrIndicators
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact span_mul_mem (hf a (Finset.mem_insert_self a s))
      (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))


lemma matcher_mem (e : E) (b : Bool) :
    (fun ω : ConfigSpace E => if ω e = b then (1 : ℝ) else 0)
      ∈ Submodule.span ℝ (incrIndicators E) := by
  cases b with
  | true =>
    have h : (fun ω : ConfigSpace E => if ω e = true then (1 : ℝ) else 0)
        = ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω; rw [Set.indicator_apply]; simp [Set.mem_setOf_eq]
    rw [h]; exact Submodule.subset_span (openIndicator_mem e)
  | false =>
    have h : (fun ω : ConfigSpace E => if ω e = false then (1 : ℝ) else 0)
        = (1 : ConfigSpace E → ℝ) - ({ω : ConfigSpace E | ω e = true}).indicator 1 := by
      ext ω
      simp only [Pi.sub_apply, Pi.one_apply, Set.indicator_apply, Set.mem_setOf_eq]
      cases hb : ω e <;> simp
    rw [h]
    exact sub_mem (Submodule.subset_span one_mem_incrIndicators)
      (Submodule.subset_span (openIndicator_mem e))


end FK
end StatMech
