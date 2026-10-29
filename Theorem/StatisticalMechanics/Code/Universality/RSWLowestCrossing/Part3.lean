/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing.Part3
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_mem_exploredSupport {N : ℕ} [DecidableEq E]
    {T : Fin N → Finset E} {i j : Fin N} (hji : j ≤ i) {e : E} (he : e ∈ T j) :
    e ∈ rlc_exploredSupport T i := by
  classical
  simp only [rlc_exploredSupport, Finset.mem_biUnion, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact ⟨j, hji, he⟩


theorem rlc_firstWitness_dependsOn {N : ℕ} [DecidableEq E]
    (W : Fin N → Set (ConfigSpace E)) (T : Fin N → Finset E)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (i : Fin N) :
    DependsOn ((rlc_firstWitness W i).indicator (fun _ => (1 : ℝ)))
      (rlc_exploredSupport T i : Set E) := by
  intro omega omega' hagree
  have hwiff : ∀ j : Fin N, j ≤ i → (omega ∈ W j ↔ omega' ∈ W j) := by
    intro j hji
    apply indic_iff
    apply hW j
    intro e he
    exact hagree e (rlc_mem_exploredSupport hji he)
  have hfirst : omega ∈ rlc_firstWitness W i ↔ omega' ∈ rlc_firstWitness W i := by
    rw [rlc_mem_firstWitness_iff, rlc_mem_firstWitness_iff]
    constructor
    · rintro ⟨hi, hmin⟩
      refine ⟨(hwiff i le_rfl).mp hi, ?_⟩
      intro j hji hj'
      exact hmin j hji ((hwiff j hji.le).mpr hj')
    · rintro ⟨hi, hmin⟩
      refine ⟨(hwiff i le_rfl).mpr hi, ?_⟩
      intro j hji hj
      exact hmin j hji ((hwiff j hji.le).mp hj)
  by_cases hmem : omega ∈ rlc_firstWitness W i
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hfirst.mp hmem)]
  · rw [Set.indicator_of_notMem hmem,
      Set.indicator_of_notMem (fun h => hmem (hfirst.mpr h))]


theorem rlc_firstWitness_inter_pairwiseDisjoint {N : ℕ}
    (W X : Fin N → Set (ConfigSpace E)) :
    Pairwise (Disjoint on fun i => rlc_firstWitness W i ∩ X i) := by
  intro i j hij
  exact (rlc_firstWitness_pairwiseDisjoint W hij).mono inter_subset_left inter_subset_left


theorem rlc_exploration_lower_bound {N : ℕ} [Countable E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1)
    (W X : Fin N → Set (ConfigSpace E))
    (T U : Fin N → Finset E) (Goal : Set (ConfigSpace E)) (c : ℝ)
    (_hc : 0 ≤ c)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
    (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
    c * (bernoulliProductMeasure (E := E) p hp).real (⋃ i, W i)
      ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  classical
  let mu := bernoulliProductMeasure (E := E) p hp
  let F : Fin N → Set (ConfigSpace E) := fun i => rlc_firstWitness W i ∩ X i
  have hfirstDep : ∀ i, DependsOn
      ((rlc_firstWitness W i).indicator (fun _ => (1 : ℝ)))
      (rlc_exploredSupport T i : Set E) :=
    fun i => rlc_firstWitness_dependsOn W T hW i
  have hfirstMeas : ∀ i, MeasurableSet (rlc_firstWitness W i) :=
    fun i => measurableSet_of_dependsOn (hfirstDep i)
  have hFMeas : ∀ i, MeasurableSet (F i) := by
    intro i
    exact (hfirstMeas i).inter (measurableSet_of_dependsOn (hX i))
  have hfactor : ∀ i, mu.real (F i) =
      mu.real (rlc_firstWitness W i) * mu.real (X i) := by
    intro i
    exact indep_cylinder_inf p hp _ _ _ _ (hdisj i) (hfirstDep i) (hX i)
  have hterm : ∀ i, c * mu.real (rlc_firstWitness W i) ≤ mu.real (F i) := by
    intro i
    rw [hfactor i, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hprob i) measureReal_nonneg
  have hFsub : (⋃ i, F i) ⊆ Goal := by
    intro omega homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨i, hi⟩ := homega
    exact hglue i hi
  calc
    c * mu.real (⋃ i, W i)
        = c * ∑ i, mu.real (rlc_firstWitness W i) := by
          rw [← rlc_iUnion_firstWitness W,
            measureReal_iUnion_fintype (rlc_firstWitness_pairwiseDisjoint W) hfirstMeas]
    _ = ∑ i, c * mu.real (rlc_firstWitness W i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, mu.real (F i) := Finset.sum_le_sum fun i _ => hterm i
    _ = mu.real (⋃ i, F i) :=
      (measureReal_iUnion_fintype (rlc_firstWitness_inter_pairwiseDisjoint W X) hFMeas).symm
    _ ≤ mu.real Goal := measureReal_mono hFsub (measure_ne_top mu Goal)


theorem rlc_stoppingPartition_lower_bound {I : Type*} [Fintype I]
    [Countable E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1)
    (H Goal : Set (ConfigSpace E))
    (Part X : I → Set (ConfigSpace E))
    (T U : I → Finset E) (c : ℝ) (_hc : 0 ≤ c)
    (hpart : (⋃ i, Part i) = H)
    (hpair : Pairwise (Disjoint on Part))
    (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (T i) (U i))
    (hprob : ∀ i, c ≤ (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
    c * (bernoulliProductMeasure (E := E) p hp).real H
      ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  classical
  let mu := bernoulliProductMeasure (E := E) p hp
  let F : I → Set (ConfigSpace E) := fun i => Part i ∩ X i
  have hPartMeas : ∀ i, MeasurableSet (Part i) :=
    fun i => measurableSet_of_dependsOn (hPart i)
  have hXMeas : ∀ i, MeasurableSet (X i) :=
    fun i => measurableSet_of_dependsOn (hX i)
  have hFMeas : ∀ i, MeasurableSet (F i) :=
    fun i => (hPartMeas i).inter (hXMeas i)
  have hFpair : Pairwise (Disjoint on F) := by
    intro i j hij
    exact (hpair hij).mono inter_subset_left inter_subset_left
  have hfactor : ∀ i,
      mu.real (F i) = mu.real (Part i) * mu.real (X i) := by
    intro i
    exact indep_cylinder_inf p hp _ _ _ _ (hdisj i) (hPart i) (hX i)
  have hterm : ∀ i, c * mu.real (Part i) ≤ mu.real (F i) := by
    intro i
    rw [hfactor i, mul_comm c]
    exact mul_le_mul_of_nonneg_left (hprob i) measureReal_nonneg
  have hFsub : (⋃ i, F i) ⊆ Goal := by
    intro omega homega
    simp only [Set.mem_iUnion] at homega
    obtain ⟨i, hi⟩ := homega
    exact hglue i hi
  calc
    c * mu.real H = c * ∑ i, mu.real (Part i) := by
      rw [← hpart, measureReal_iUnion_fintype hpair hPartMeas]
    _ = ∑ i, c * mu.real (Part i) := by rw [Finset.mul_sum]
    _ ≤ ∑ i, mu.real (F i) := Finset.sum_le_sum fun i _ => hterm i
    _ = mu.real (⋃ i, F i) :=
      (measureReal_iUnion_fintype hFpair hFMeas).symm
    _ ≤ mu.real Goal := measureReal_mono hFsub (measure_ne_top mu Goal)


theorem rlc_bernoulli_rsw_stopping_sixth_power
    {I : Type*} [Fintype I] [Countable E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (E₀ E₁ Goal : Set (ConfigSpace E))
    (S₀ S₁ : Finset E)
    (hE₀inc : IsIncreasing E₀) (hE₁inc : IsIncreasing E₁)
    (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
    (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
    (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
    (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
    (Part X : I → Set (ConfigSpace E))
    (T U : I → Finset E)
    (hpart : (⋃ i, Part i) = E₀ ∩ E₁)
    (hpair : Pairwise (Disjoint on Part))
    (hPart : ∀ i, DependsOn ((Part i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (T i) (U i))
    (hconnector : ∀ i, (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, Part i ∩ X i ⊆ Goal) :
    α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hdiag : μ.real E₀ * μ.real E₁ ≤ μ.real (E₀ ∩ E₁) :=
    rlc_harris_cylinder p hp hE₀inc hE₁inc S₀ S₁ hE₀dep hE₁dep
  have hdiagLower : (α ^ 3 / 4) * (α ^ 3 / 4) ≤ μ.real E₀ * μ.real E₁ := by
    exact mul_le_mul hE₀prob hE₁prob (by positivity) measureReal_nonneg
  have hexplore : (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) ≤ μ.real Goal :=
    rlc_stoppingPartition_lower_bound p hp (E₀ ∩ E₁) Goal Part X T U (1 / 2)
      (by norm_num) hpart hpair hPart hX hdisj hconnector hglue
  calc
    α ^ 6 / 32 = (1 : ℝ) / 2 * ((α ^ 3 / 4) * (α ^ 3 / 4)) := by ring
    _ ≤ (1 : ℝ) / 2 * (μ.real E₀ * μ.real E₁) :=
      mul_le_mul_of_nonneg_left hdiagLower (by norm_num)
    _ ≤ (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) :=
      mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ ≤ μ.real Goal := hexplore


theorem rlc_bernoulli_rsw_sixth_power {N : ℕ} [Countable E] [DecidableEq E]
    (p : NNReal) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (E₀ E₁ Goal : Set (ConfigSpace E))
    (S₀ S₁ : Finset E)
    (hE₀inc : IsIncreasing E₀) (hE₁inc : IsIncreasing E₁)
    (hE₀dep : DependsOn (E₀.indicator (fun _ => (1 : ℝ))) (S₀ : Set E))
    (hE₁dep : DependsOn (E₁.indicator (fun _ => (1 : ℝ))) (S₁ : Set E))
    (hE₀prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₀)
    (hE₁prob : α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real E₁)
    (W X : Fin N → Set (ConfigSpace E))
    (T U : Fin N → Finset E)
    (hpartition : (⋃ i, W i) = E₀ ∩ E₁)
    (hW : ∀ i, DependsOn ((W i).indicator (fun _ => (1 : ℝ))) (T i : Set E))
    (hX : ∀ i, DependsOn ((X i).indicator (fun _ => (1 : ℝ))) (U i : Set E))
    (hdisj : ∀ i, Disjoint (rlc_exploredSupport T i) (U i))
    (hconnector : ∀ i, (1 : ℝ) / 2 ≤
      (bernoulliProductMeasure (E := E) p hp).real (X i))
    (hglue : ∀ i, rlc_firstWitness W i ∩ X i ⊆ Goal) :
    α ^ 6 / 32 ≤ (bernoulliProductMeasure (E := E) p hp).real Goal := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hdiag : μ.real E₀ * μ.real E₁ ≤ μ.real (E₀ ∩ E₁) :=
    rlc_harris_cylinder p hp hE₀inc hE₁inc S₀ S₁ hE₀dep hE₁dep
  have hdiagLower : (α ^ 3 / 4) * (α ^ 3 / 4) ≤ μ.real E₀ * μ.real E₁ := by
    exact mul_le_mul hE₀prob hE₁prob (by positivity) measureReal_nonneg
  have hexplore : (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) ≤ μ.real Goal := by
    rw [← hpartition]
    exact rlc_exploration_lower_bound p hp W X T U Goal (1 / 2)
      (by norm_num) hW hX hdisj hconnector hglue
  calc
    α ^ 6 / 32 = (1 : ℝ) / 2 * ((α ^ 3 / 4) * (α ^ 3 / 4)) := by ring
    _ ≤ (1 : ℝ) / 2 * (μ.real E₀ * μ.real E₁) := by
      exact mul_le_mul_of_nonneg_left hdiagLower (by norm_num)
    _ ≤ (1 : ℝ) / 2 * μ.real (E₀ ∩ E₁) := by
      exact mul_le_mul_of_nonneg_left hdiag (by norm_num)
    _ ≤ μ.real Goal := hexplore


end Universality
end StatMech
