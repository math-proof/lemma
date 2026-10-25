/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/InhomogeneousParityAvoidance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.NonnegativeCurrentConditionalPMF.Part5
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxEvenLimit.Part6
import Def.StatisticalMechanics.Code.FrontierB.InhomogeneousParityAvoidance.Part2
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem boltzmannJ_mul_exp_neg_weightedEdgeSpinSum
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset)
    (s : ConfigSpace V) :
    boltzmannJ G beta J s *
        Real.exp (-weightedEdgeSpinSum beta J F s) =
      boltzmannJ G beta (inhomogeneousDeletedCoupling J F) s := by
  unfold boltzmannJ weightedEdgeSpinSum inhomogeneousDeletedCoupling
  rw [← Real.exp_add]
  congr 1
  have hsplit :
      (∑ e ∈ G.edgeFinset \ F, J e * bond s e) +
          ∑ e ∈ F, J e * bond s e =
        ∑ e ∈ G.edgeFinset, J e * bond s e :=
    Finset.sum_sdiff hF
  have hdeleted :
      (∑ e ∈ G.edgeFinset,
        (if e ∈ F then 0 else J e) * bond s e) =
        ∑ e ∈ G.edgeFinset \ F, J e * bond s e := by
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.sdiff_subset)
    · intro e heGap
      have heE : e ∈ G.edgeFinset := (Finset.mem_sdiff.mp heGap).1
      have heNot : e ∉ G.edgeFinset \ F := (Finset.mem_sdiff.mp heGap).2
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.mpr ⟨heE, hef⟩)
      simp [heF]
    · intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.mp heDiff).2
      simp [heF]
  rw [hdeleted, ← hsplit, Finset.mul_sum]
  have hmul (S : Finset (Sym2 V)) :
      (∑ e ∈ S, beta * J e * bond s e) =
        beta * ∑ e ∈ S, J e * bond s e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  rw [hmul F]
  have hdiff :
      (∑ e ∈ G.edgeFinset \ F, beta * (J e * bond s e)) =
        beta * ∑ e ∈ G.edgeFinset \ F, J e * bond s e := by
    symm
    rw [Finset.mul_sum]
  rw [hdiff]
  ring

theorem inhomogeneousDeletedCoupling_cosh_prod
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    (∏ e ∈ G.edgeFinset,
      Real.cosh (beta * inhomogeneousDeletedCoupling J F e)) =
      ∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e) := by
  calc
    (∏ e ∈ G.edgeFinset,
        Real.cosh (beta * inhomogeneousDeletedCoupling J F e)) =
      ∏ e ∈ G.edgeFinset \ F,
        Real.cosh (beta * inhomogeneousDeletedCoupling J F e) := by
      symm
      apply Finset.prod_subset (Finset.sdiff_subset)
      intro e heE heNot
      have heF : e ∈ F := by
        by_contra hef
        exact heNot (Finset.mem_sdiff.mpr ⟨heE, hef⟩)
      simp [inhomogeneousDeletedCoupling, heF]
    _ = _ := by
      apply Finset.prod_congr rfl
      intro e heDiff
      have heF : e ∉ F := (Finset.mem_sdiff.mp heDiff).2
      simp [inhomogeneousDeletedCoupling, heF]

theorem inhomogeneousDeletedCoupling_highTemp_sum
    (beta : ℝ) (J : Sym2 V → ℝ) (F : Finset (Sym2 V)) :
    (∑ H ∈ G.edgeFinset.powerset.filter IsEvenSubgraph,
      highTempSubgraphWeight beta (inhomogeneousDeletedCoupling J F) H) =
      inhomogeneousParityAvoidSum G beta J F := by
  unfold inhomogeneousParityAvoidSum
  apply Finset.sum_congr rfl
  intro H hH
  by_cases hd : Disjoint H F
  · rw [if_pos hd]
    unfold highTempSubgraphWeight
    apply Finset.prod_congr rfl
    intro e heH
    have heF : e ∉ F := fun hef => Finset.disjoint_left.mp hd heH hef
    simp [inhomogeneousDeletedCoupling, heF]
  · rw [if_neg hd]
    unfold highTempSubgraphWeight
    have hinter : (H ∩ F).Nonempty := by
      rw [Finset.not_disjoint_iff_nonempty_inter] at hd
      exact hd
    obtain ⟨e, he⟩ := hinter
    have heH : e ∈ H := (Finset.mem_inter.mp he).1
    have heF : e ∈ F := (Finset.mem_inter.mp he).2
    apply Finset.prod_eq_zero heH
    simp [inhomogeneousDeletedCoupling, heF]

theorem partitionJ_inhomogeneousDeleted_highTemp
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    partitionJ G beta (inhomogeneousDeletedCoupling J F) =
      (2 : ℝ) ^ Fintype.card V *
        (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          inhomogeneousParityAvoidSum G beta J F := by
  rw [partitionJ_eq_cosh_mul_inhomogeneousParityPartition,
    inhomogeneousDeletedCoupling_cosh_prod G beta J F hF]
  congr 1
  exact inhomogeneousDeletedCoupling_highTemp_sum G beta J F


theorem inhomogeneousParityAvoidRatio_eq_spinExpectation
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    inhomogeneousParityAvoidSum G beta J F /
        inhomogeneousParityPartition G beta J =
      ((∑ s : ConfigSpace V,
          boltzmannJ G beta J s *
            Real.exp (-weightedEdgeSpinSum beta J F s)) /
        partitionJ G beta J) *
          ∏ e ∈ F, Real.cosh (beta * J e) := by
  have hnum :
      (∑ s : ConfigSpace V,
          boltzmannJ G beta J s *
            Real.exp (-weightedEdgeSpinSum beta J F s)) =
        partitionJ G beta (inhomogeneousDeletedCoupling J F) := by
    unfold partitionJ
    apply Finset.sum_congr rfl
    intro s hs
    exact boltzmannJ_mul_exp_neg_weightedEdgeSpinSum
      G beta J F hF s
  rw [hnum, partitionJ_inhomogeneousDeleted_highTemp G beta J F hF,
    partitionJ_eq_cosh_mul_inhomogeneousParityPartition]
  have htwo : (2 : ℝ) ^ Fintype.card V ≠ 0 := by positivity
  have houtside : (∏ e ∈ G.edgeFinset \ F,
      Real.cosh (beta * J e)) ≠ 0 := by positivity
  have hinside : (∏ e ∈ F, Real.cosh (beta * J e)) ≠ 0 := by
    positivity
  have hpart : inhomogeneousParityPartition G beta J ≠ 0 := by
    intro hz
    have hEq := partitionJ_eq_cosh_mul_inhomogeneousParityPartition G beta J
    rw [hz, mul_zero] at hEq
    exact (ne_of_gt (partitionJ_pos G beta J)) hEq
  have hprod :
      (∏ e ∈ G.edgeFinset \ F, Real.cosh (beta * J e)) *
          ∏ e ∈ F, Real.cosh (beta * J e) =
        ∏ e ∈ G.edgeFinset, Real.cosh (beta * J e) :=
    Finset.prod_sdiff hF
  field_simp
  rw [← hprod]
  ring

theorem inhomogeneousParityAvoidRatio_eq_expJ
    (beta : ℝ) (J : Sym2 V → ℝ)
    (F : Finset (Sym2 V)) (hF : F ⊆ G.edgeFinset) :
    inhomogeneousParityAvoidSum G beta J F /
        inhomogeneousParityPartition G beta J =
      expJ G.edgeFinset (fun e => beta * J e) (fun _ => 0)
          (fun s => Real.exp (-weightedEdgeSpinSum beta J F s)) *
        ∏ e ∈ F, Real.cosh (beta * J e) := by
  rw [inhomogeneousParityAvoidRatio_eq_spinExpectation G beta J F hF]
  congr 1
  unfold expJ ZJ wJ partitionJ boltzmannJ
  simp only [zero_mul, Finset.sum_const_zero, add_zero]
  have hexp (s : ConfigSpace V) :
      beta * (∑ e ∈ G.edgeFinset, J e * bond s e) =
        ∑ e ∈ G.edgeFinset, beta * J e * bond s e := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    ring
  simp_rw [hexp]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  ring


theorem sourcelessCurrentMeasure_parityAvoid_inhomogeneous
    (beta : ℝ) (hbeta : 0 < beta) (J : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (F : Finset (Sym2 V)) :
    (sourcelessCurrentPMF G beta J hbeta.le hJ).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      ENNReal.ofReal
        (inhomogeneousParityAvoidSum G beta J F /
          inhomogeneousParityPartition G beta J) := by
  calc
    (sourcelessCurrentPMF G beta J hbeta.le hJ).toMeasure
        {m | Disjoint (currentParitySupport G m) F} =
      (sourcelessNonnegativeParityPMF G beta J hbeta.le hJ).toMeasure
        {H | Disjoint H F} := by
      rw [sourcelessNonnegativeParityPMF, PMF.toMeasure_map_apply]
      · rfl
      · exact Measurable.of_discrete
      · exact MeasurableSet.of_discrete
    _ = _ := sourcelessNonnegativeParityMeasure_avoid
      G beta hbeta J hJ F

end StatMech.FrontierB
