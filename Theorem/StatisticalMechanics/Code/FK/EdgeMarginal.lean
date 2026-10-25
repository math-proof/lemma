/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/EdgeMarginal.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Inequalities.IncreasingEvent.Part2
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.FKG
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Structure.StatisticalMechanics.Code.FK.EdgeMarginal
open scoped BigOperators
open SimpleGraph


namespace StatMech

namespace FK

variable {E : Type*} [Fintype E] [DecidableEq E]


lemma bool_eq_of_le_ne {b c : Bool} (hle : b ≤ c) (hne : b ≠ c) :
    b = false ∧ c = true := by
  revert hle hne; cases b <;> cases c <;> decide

lemma boolR_mono {b c : Bool} (h : b ≤ c) :
    (if b then (1 : ℝ) else 0) ≤ (if c then (1 : ℝ) else 0) := by
  cases b <;> cases c <;> simp_all (config := { decide := true })

lemma boolR_diff_nonneg {b c : Bool} (h : b ≤ c) :
    (0 : ℝ) ≤ (if c then (1 : ℝ) else 0) - (if b then (1 : ℝ) else 0) := by
  have := boolR_mono h; linarith

omit [DecidableEq E] in


theorem indicator_diff_le_edgeSum {A : Set (ConfigSpace E)} (hA : IsIncreasing A)
    {ω ω' : ConfigSpace E} (h : ω ≤ ω') :
    A.indicator (fun _ => (1 : ℝ)) ω' - A.indicator (fun _ => (1 : ℝ)) ω
      ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) := by
  have hsumnn : (0 : ℝ)
      ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) :=
    Finset.sum_nonneg (fun e _ => boolR_diff_nonneg (h e))
  by_cases hmem : ω ∈ A
  · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem (hA h hmem)]; simpa using hsumnn
  · rw [Set.indicator_of_notMem hmem, sub_zero]
    by_cases hmem' : ω' ∈ A
    · rw [Set.indicator_of_mem hmem']
      have hne : ω ≠ ω' := fun heq => hmem (heq ▸ hmem')
      obtain ⟨e, he⟩ : ∃ e, ω e ≠ ω' e := by
        by_contra hcon
        exact hne (funext fun e => not_not.mp (fun h => hcon ⟨e, h⟩))
      have hbc : ω e = false ∧ ω' e = true := bool_eq_of_le_ne (h e) he
      calc (1 : ℝ)
          = (if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0) := by
            rw [hbc.1, hbc.2]; norm_num
        _ ≤ ∑ e : E, ((if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0)) :=
            Finset.single_le_sum
              (f := fun e => (if ω' e then (1 : ℝ) else 0) - (if ω e then (1 : ℝ) else 0))
              (fun i _ => boolR_diff_nonneg (h i)) (Finset.mem_univ e)
    · rw [Set.indicator_of_notMem hmem']; exact hsumnn


theorem eventMass_eq_coupling_snd {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (A : Set (ConfigSpace E)) :
    eventMassProb ν A
      = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.2 * P z := by
  unfold eventMassProb
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω' _ => by rw [← hP.snd_marginal ω', Finset.mul_sum]


theorem eventMass_eq_coupling_fst {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (A : Set (ConfigSpace E)) :
    eventMassProb μ A
      = ∑ z : ConfigSpace E × ConfigSpace E, A.indicator (fun _ => (1 : ℝ)) z.1 * P z := by
  unfold eventMassProb
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => by rw [← hP.fst_marginal ω, Finset.mul_sum]


theorem edgeMarg_eq_coupling_snd {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν) (e : E) :
    edgeMargProb ν e
      = ∑ z : ConfigSpace E × ConfigSpace E, (if z.2 e then (1 : ℝ) else 0) * P z := by
  unfold edgeMargProb
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_congr rfl fun ω' _ => by rw [← hP.snd_marginal ω', Finset.mul_sum]


theorem edgeMarg_eq_coupling_fst {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν) (e : E) :
    edgeMargProb μ e
      = ∑ z : ConfigSpace E × ConfigSpace E, (if z.1 e then (1 : ℝ) else 0) * P z := by
  unfold edgeMargProb
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun ω _ => by rw [← hP.fst_marginal ω, Finset.mul_sum]


theorem eventMass_diff_le_edgeMarg_sum {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb ν A - eventMassProb μ A
      ≤ ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) := by
  rw [eventMass_eq_coupling_snd hP, eventMass_eq_coupling_fst hP, ← Finset.sum_sub_distrib]
  have hRHS : ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e)
      = ∑ z : ConfigSpace E × ConfigSpace E,
          (∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))) * P z := by
    rw [Finset.sum_congr rfl (fun e _ => by
        rw [edgeMarg_eq_coupling_snd hP e, edgeMarg_eq_coupling_fst hP e,
          ← Finset.sum_sub_distrib])]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun e _ => by ring
  rw [hRHS]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : z.1 ≤ z.2
  · have hcore := indicator_diff_le_edgeSum hA hz
    have hPnn := hP.nonneg z
    calc A.indicator (fun _ => (1 : ℝ)) z.2 * P z - A.indicator (fun _ => (1 : ℝ)) z.1 * P z
        = (A.indicator (fun _ => (1 : ℝ)) z.2 - A.indicator (fun _ => (1 : ℝ)) z.1) * P z := by
          ring
      _ ≤ (∑ e : E, ((if z.2 e then (1 : ℝ) else 0) - (if z.1 e then (1 : ℝ) else 0))) * P z :=
          mul_le_mul_of_nonneg_right hcore hPnn
  · rw [hP.supportLE z hz]; simp


theorem coupling_eventMass_le {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A ≤ eventMassProb ν A := by
  rw [eventMass_eq_coupling_snd hP, eventMass_eq_coupling_fst hP]
  refine Finset.sum_le_sum fun z _ => ?_
  by_cases hz : z.1 ≤ z.2
  · exact mul_le_mul_of_nonneg_right (hA.indicator_monotone hz) (hP.nonneg z)
  · rw [hP.supportLE z hz]; simp


theorem eventMass_eq_of_edgeMarg_eq {P : ConfigSpace E × ConfigSpace E → ℝ}
    {μ ν : ConfigSpace E → ℝ} (hP : IsMonotoneCouplingFun P μ ν)
    (hmarg : ∀ e : E, edgeMargProb μ e = edgeMargProb ν e)
    {A : Set (ConfigSpace E)} (hA : IsIncreasing A) :
    eventMassProb μ A = eventMassProb ν A := by
  refine le_antisymm (coupling_eventMass_le hP hA) ?_
  have hsum : ∑ e : E, (edgeMargProb ν e - edgeMargProb μ e) = 0 :=
    Finset.sum_eq_zero fun e _ => by rw [hmarg e]; ring
  have h := eventMass_diff_le_edgeMarg_sum hP hA
  rw [hsum] at h; linarith


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


theorem edgeMargProb_fkProb (p q : ℝ) (e : Sym2 V) :
    edgeMargProb (fkProb G p q) e = edgeMarginalOpen G p q e := by
  unfold edgeMargProb edgeMarginalOpen
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun ω _ => ?_
  by_cases h : ω e <;> simp [h]


end FK
end StatMech
