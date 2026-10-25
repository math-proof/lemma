/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/CompleteFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Topology.UniformSpace.Completion
import Mathlib.Topology.UniformSpace.AbstractCompletion
import Mathlib.Topology.Algebra.UniformField
import Mathlib.Topology.Algebra.UniformRing
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.Normed.Ring.WithAbs
import Mathlib.Analysis.AbsoluteValue.Equivalence
import Mathlib.NumberTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Ideal.Over
import Def.v1.Atlas.NumberTheoryI.code.Chapter1.AbsoluteValues.Part2
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.Chapter1.AbsoluteValues
import Abbrev.v1.Atlas.NumberTheoryI.code.CompleteFields


noncomputable section

open scoped Topology

open UniformSpace

example (X : Type*) [UniformSpace X] : Type _ := Completion X

example (X : Type*) [UniformSpace X] : X → Completion X := Completion.coe'

example (X : Type*) [UniformSpace X] : CompleteSpace (Completion X) :=
  Completion.completeSpace X

example (X : Type*) [UniformSpace X] : DenseRange (Completion.coe' (α := X)) :=
  Completion.denseRange_coe

example (K : Type*) [Field K] (v : AbsoluteValue K ℝ) :
    NormedRing (WithAbs v) := WithAbs.normedRing v

example (K : Type*) [Field K] (v : AbsoluteValue K ℝ)
    [IsTopologicalDivisionRing (WithAbs v)]
    [CompletableTopField (WithAbs v)]
    [IsUniformAddGroup (WithAbs v)] :
    Field (Completion (WithAbs v)) := inferInstance

set_option backward.isDefEq.respectTransparency false in
set_option synthInstance.maxHeartbeats 40000 in
set_option linter.unusedVariables false in

theorem weak_approximation_theorem
    {K : Type*} [Field K]
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → AbsoluteValue K ℝ)
    (hv_nontrivial : ∀ i, (v i).IsNontrivial)
    (hv_ineq : ∀ i j, i ≠ j → ¬ (v i).IsEquiv (v j))
    (a : ι → K) (ε : ι → ℝ) (hε : ∀ i, 0 < ε i) :
    ∃ x : K, ∀ i, v i (x - a i) < ε i := by
  classical
  open Filter Topology Finset in
  have hpw : Pairwise fun i j => ¬(v i).IsEquiv (v j) := fun i j hij => hv_ineq i j hij
  choose xl hxl using
    AbsoluteValue.exists_one_lt_lt_one_pi_of_not_isEquiv hv_nontrivial hpw
  let y : ℕ → K := fun n => ∑ i, a i * (1 / (1 + (xl i)⁻¹ ^ n))
  suffices ∀ j, ∃ N, ∀ n, N ≤ n → (v j) (y n - a j) < ε j by
    choose N hN using this
    exact ⟨y (Finset.univ.sup N), fun j => hN j _ (Finset.le_sup (Finset.mem_univ j))⟩
  intro j
  have hconv : Tendsto (fun n => (WithAbs.equiv (v j)).symm (y n)) atTop
      (nhds ((WithAbs.equiv (v j)).symm (a j))) := by
    simp only [y, map_sum, map_mul]
    conv_rhs => rw [show (WithAbs.equiv (v j)).symm (a j) =
      ∑ i : ι, if i = j then (WithAbs.equiv (v j)).symm (a i) else 0 from by simp]
    apply tendsto_finset_sum
    intro i _
    by_cases hi : i = j
    · simp only [hi, ite_true]
      have hinv : (v j) (xl j)⁻¹ < 1 := by
        rw [map_inv₀]; exact inv_lt_one_of_one_lt₀ (hxl j).1
      have h := (WithAbs.tendsto_one_div_one_add_pow_nhds_one hinv).const_mul
        ((WithAbs.equiv (v j)).symm (a j))
      rwa [show (WithAbs.equiv (v j)).symm (a j) * (1 : WithAbs (v j)) =
        (WithAbs.equiv (v j)).symm (a j) from mul_one _] at h
    · simp only [hi, ite_false]
      have hxl_ne : xl i ≠ 0 := by
        intro h; have := (hxl i).1; simp [h] at this; linarith
      have hinv : 1 < (v j) (xl i)⁻¹ := by
        rw [map_inv₀, one_lt_inv₀ ((v j).pos hxl_ne)]
        exact (hxl i).2 j (Ne.symm hi)
      have htend_real := (v j).tendsto_div_one_add_pow_nhds_zero hinv
      simp_rw [← WithAbs.norm_toAbs_eq] at htend_real
      have htend_zero := tendsto_zero_iff_norm_tendsto_zero.mpr htend_real
      have h := htend_zero.const_mul ((WithAbs.equiv (v j)).symm (a i))
      rwa [show (WithAbs.equiv (v j)).symm (a i) * (0 : WithAbs (v j)) =
        (0 : WithAbs (v j)) from mul_zero _] at h
  have hconv_norm : Tendsto (fun n => (v j) (y n - a j)) atTop (nhds 0) := by
    rw [Metric.tendsto_atTop] at hconv ⊢
    intro ε' hε'
    obtain ⟨N, hN⟩ := hconv ε' hε'
    exact ⟨N, fun n hn => by
      specialize hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((v j).nonneg _)]
      rw [dist_eq_norm, show (WithAbs.equiv (v j)).symm (y n) - (WithAbs.equiv (v j)).symm (a j) =
        (WithAbs.equiv (v j)).symm (y n - a j) from by simp [map_sub]] at hN
      rw [WithAbs.norm_toAbs_eq] at hN
      exact hN⟩
  exact (Metric.tendsto_atTop.1 hconv_norm (ε j) (hε j)).imp fun N hN =>
    fun n hn => by
      specialize hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg ((v j).nonneg _)] at hN
      exact hN

end
