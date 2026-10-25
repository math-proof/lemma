/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Foundations/StrassenFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Foundations.Strassen
import Def.StatisticalMechanics.Code.Foundations.StrassenFull.Part3
open MeasureTheory Finset
open scoped RealInnerProductSpace

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false


namespace StatMech

namespace Transport

open Filter Topology


variable {P : Type*} [Fintype P] [DecidableEq P] [PartialOrder P]


variable [DecidableRel ((· ≤ ·) : P → P → Prop)]


open ProperCone Set


theorem mem_orthant (y : EuclideanSpace ℝ (OrderPairs P)) :
    y ∈ orthant P ↔ ∀ q, 0 ≤ y q := by
  simp only [orthant, mem_innerDual]
  constructor
  · intro h q
    simpa [EuclideanSpace.inner_single_left] using h (Set.mem_range_self q)
  · rintro h x ⟨q, rfl⟩
    simpa [EuclideanSpace.inner_single_left] using h q

theorem inner_eq_sum (x y : EuclideanSpace ℝ (OrderPairs P)) :
    (inner ℝ x y : ℝ) = ∑ q, x q * y q := by
  rw [PiLp.inner_apply]; simp [RCLike.inner_apply, mul_comm]


theorem orthant_selfdual :
    innerDual ((orthant P : Set (EuclideanSpace ℝ (OrderPairs P)))) = orthant P := by
  apply le_antisymm
  · intro y hy
    rw [mem_orthant]; intro q; rw [mem_innerDual] at hy
    have hpos : (0 : ℝ) ≤ (inner ℝ (EuclideanSpace.single q (1 : ℝ)) y : ℝ) := by
      apply hy; rw [SetLike.mem_coe, mem_orthant]; intro j
      rcases eq_or_ne q j with rfl | hne
      · simp
      · simp [hne, eq_comm]
    simpa [EuclideanSpace.inner_single_left] using hpos
  · intro y hy; rw [mem_innerDual]; intro x hx
    rw [SetLike.mem_coe, mem_orthant] at hx; rw [mem_orthant] at hy
    rw [inner_eq_sum]
    exact Finset.sum_nonneg (fun q _ => mul_nonneg (hx q) (hy q))


theorem exists_coupling_vec [Nonempty P] (μ ν : P → ℝ)
    (hμpos : ∀ x, 0 ≤ μ x) (hνpos : ∀ x, 0 ≤ ν x)
    (hTOT : ∑ x, μ x = ∑ x, ν x)
    (hDOM : ∀ D : Finset P, IsDown D → ∑ x ∈ D, ν x ≤ ∑ x ∈ D, μ x) :
    ∃ c : OrderPairs P → ℝ, (∀ q, 0 ≤ c q) ∧
      (∀ x, (∑ q : OrderPairs P, if (q : P × P).1 = x then c q else 0) = μ x) ∧
      (∀ y, (∑ q : OrderPairs P, if (q : P × P).2 = y then c q else 0) = ν y) := by
  classical
  set b : EuclideanSpace ℝ (P ⊕ P) := (WithLp.equiv 2 _).symm
    (fun s => match s with | Sum.inl x => μ x | Sum.inr y => ν y) with hbdef
  have hbinl : ∀ x, b (Sum.inl x) = μ x := fun x => rfl
  have hbinr : ∀ y, b (Sum.inr y) = ν y := fun y => rfl
  
  have hmem : b ∈ ProperCone.map margCLM (orthant P) := by
    rw [ProperCone.relative_hyperplane_separation]
    intro w hw
    rw [orthant_selfdual, mem_orthant] at hw
    have hfeas : ∀ x y : P, x ≤ y → 0 ≤ w (Sum.inl x) + w (Sum.inr y) := by
      intro x y hxy
      have hwq := hw ⟨(x, y), hxy⟩
      have key : (ContinuousLinearMap.adjoint margCLM w) (⟨(x, y), hxy⟩ : OrderPairs P)
          = w (Sum.inl x) + w (Sum.inr y) := by
        have h1 : (inner ℝ (EuclideanSpace.single (⟨(x, y), hxy⟩ : OrderPairs P) (1 : ℝ))
              (ContinuousLinearMap.adjoint margCLM w) : ℝ)
            = (ContinuousLinearMap.adjoint margCLM w) (⟨(x, y), hxy⟩ : OrderPairs P) := by
          rw [EuclideanSpace.inner_single_left]; simp
        rw [← h1, ContinuousLinearMap.adjoint_inner_right, marg_inner]
        simp only [PiLp.single_apply]
        rw [Finset.sum_eq_single (⟨(x, y), hxy⟩ : OrderPairs P)]
        · simp
        · intro q _ hqne; simp [hqne]
        · intro hc; exact absurd (Finset.mem_univ _) hc
      rw [key] at hwq; exact hwq
    rw [show (inner ℝ b w : ℝ)
          = (∑ x, b (Sum.inl x) * w (Sum.inl x)) + ∑ y, b (Sum.inr y) * w (Sum.inr y) by
      rw [PiLp.inner_apply, Fintype.sum_sum_type]
      simp only [RCLike.inner_apply, conj_trivial]
      congr 1 <;> exact Finset.sum_congr rfl (fun x _ => by ring)]
    simp only [hbinl, hbinr]
    exact dual_feasibility μ ν hμpos hνpos hTOT hDOM
      (fun x => w (Sum.inl x)) (fun y => w (Sum.inr y)) hfeas
  
  
  set base : Set (EuclideanSpace ℝ (P ⊕ P)) :=
    margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | (∀ q, 0 ≤ c q) ∧ ∑ q, c q = 1} with hbasedef
  have hsimplex_compact : IsCompact
      {c : EuclideanSpace ℝ (OrderPairs P) | (∀ q, 0 ≤ c q) ∧ ∑ q, c q = 1} := by
    apply Metric.isCompact_of_isClosed_isBounded
    · 
      have h1 : IsClosed {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
        rw [show {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q}
            = ⋂ q, {c : EuclideanSpace ℝ (OrderPairs P) | 0 ≤ c q} by ext c; simp]
        exact isClosed_iInter (fun q =>
          isClosed_le continuous_const ((EuclideanSpace.proj q).continuous))
      have h2 : IsClosed {c : EuclideanSpace ℝ (OrderPairs P) | ∑ q, c q = 1} := by
        have hcont : Continuous (fun c : EuclideanSpace ℝ (OrderPairs P) => ∑ q, c q) :=
          continuous_finsetSum _ (fun q _ => (EuclideanSpace.proj q).continuous)
        exact isClosed_eq hcont continuous_const
      exact h1.inter h2
    · 
      apply Metric.isBounded_iff_subset_closedBall (0 : EuclideanSpace ℝ (OrderPairs P)) |>.2
      refine ⟨Real.sqrt (Fintype.card (OrderPairs P)), fun c hc => ?_⟩
      simp only [Set.mem_setOf_eq] at hc
      obtain ⟨hcpos, hcsum⟩ := hc
      rw [Metric.mem_closedBall, dist_zero_right]
      have hbd : ∀ q, c q ≤ 1 := by
        intro q
        calc c q ≤ ∑ q', c q' := Finset.single_le_sum (fun q' _ => hcpos q') (Finset.mem_univ q)
          _ = 1 := hcsum
      rw [EuclideanSpace.norm_eq]
      apply Real.sqrt_le_sqrt
      calc ∑ q, ‖c q‖ ^ 2 ≤ ∑ q : OrderPairs P, (1:ℝ) := by
            apply Finset.sum_le_sum; intro q _
            rw [Real.norm_eq_abs, abs_of_nonneg (hcpos q), sq_le_one_iff_abs_le_one,
              abs_of_nonneg (hcpos q)]
            exact hbd q
        _ = Fintype.card (OrderPairs P) := by simp
  have hbase_compact : IsCompact base := hsimplex_compact.image margCLM.continuous
  have hbase_no0 : (0 : EuclideanSpace ℝ (P ⊕ P)) ∉ base := by
    rintro ⟨c, ⟨hcpos, hcsum⟩, hc0⟩
    
    have hrow : ∑ x : P, (margCLM c) (Sum.inl x) = 1 := by
      simp only [margCLM_inl]
      rw [Finset.sum_comm]
      rw [show (∑ q : OrderPairs P, ∑ x : P, if (q : P × P).1 = x then c q else 0)
          = ∑ q : OrderPairs P, c q from
        Finset.sum_congr rfl (fun q _ => by
          rw [Finset.sum_ite_eq Finset.univ (q : P × P).1 (fun _ => c q)]; simp)]
      exact hcsum
    rw [hc0] at hrow; simp at hrow
  have hbase_ne : base.Nonempty := by
    have hq0 : Nonempty (OrderPairs P) := ⟨⟨(Classical.arbitrary P, Classical.arbitrary P), le_refl _⟩⟩
    obtain ⟨q0⟩ := hq0
    refine ⟨margCLM (EuclideanSpace.single q0 1), EuclideanSpace.single q0 1, ⟨?_, ?_⟩, rfl⟩
    · intro q; rcases eq_or_ne q0 q with rfl | hne
      · simp
      · simp [hne]
    · rw [show (∑ q, (EuclideanSpace.single q0 (1:ℝ)) q) = ∑ q, (if q = q0 then (1:ℝ) else 0) from
        Finset.sum_congr rfl (fun q _ => by rw [PiLp.single_apply])]
      simp
  have himg_closed : IsClosed {z : EuclideanSpace ℝ (P ⊕ P) |
      ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ base, z = t • x} :=
    isClosed_nonneg_smul_of_compact base hbase_compact hbase_no0
  
  have himg_eq : (margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q})
      = {z : EuclideanSpace ℝ (P ⊕ P) | ∃ t : ℝ, 0 ≤ t ∧ ∃ x ∈ base, z = t • x} := by
    ext z
    simp only [Set.mem_image, Set.mem_setOf_eq]
    constructor
    · rintro ⟨c, hc, rfl⟩
      by_cases hz : ∑ q, c q = 0
      · 
        have hc0 : ∀ q, c q = 0 := fun q =>
          (Finset.sum_eq_zero_iff_of_nonneg (fun q _ => hc q)).1 hz q (Finset.mem_univ q)
        obtain ⟨x0, hx0⟩ := hbase_ne
        refine ⟨0, le_refl 0, x0, hx0, ?_⟩
        rw [zero_smul]
        rw [show c = 0 from PiLp.ext (fun q => by simpa using hc0 q), map_zero]
      · refine ⟨∑ q, c q, Finset.sum_nonneg (fun q _ => hc q), (∑ q, c q)⁻¹ • (margCLM c), ?_, ?_⟩
        · refine ⟨(∑ q, c q)⁻¹ • c, ⟨fun q => ?_, ?_⟩, by rw [map_smul]⟩
          · exact smul_nonneg (inv_nonneg.2 (Finset.sum_nonneg (fun q _ => hc q))) (hc q)
          · simp only [PiLp.smul_apply, smul_eq_mul]
            rw [← Finset.mul_sum, inv_mul_cancel₀ hz]
        · rw [smul_inv_smul₀ hz]
    · rintro ⟨t, ht, x, hx, rfl⟩
      obtain ⟨c, ⟨hcpos, _⟩, rfl⟩ := hx
      exact ⟨t • c, fun q => smul_nonneg ht (hcpos q), by rw [map_smul]⟩
  have hset : ((orthant P).toPointedCone : Set (EuclideanSpace ℝ (OrderPairs P)))
      = {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    ext c; rw [SetLike.mem_coe, ProperCone.mem_toPointedCone, mem_orthant]; rfl
  
  have hcoe : (((orthant P).toPointedCone.map
        ((margCLM : EuclideanSpace ℝ (OrderPairs P) →L[ℝ] EuclideanSpace ℝ (P ⊕ P)) :
          EuclideanSpace ℝ (OrderPairs P) →ₗ[ℝ] EuclideanSpace ℝ (P ⊕ P))) : Set _)
      = margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    rw [PointedCone.coe_map, hset]; rfl
  
  have hb_img : b ∈ margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
    rw [ProperCone.mem_map, PointedCone.mem_closure] at hmem
    rw [hcoe] at hmem
    have hclo : closure (margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q})
        = margCLM '' {c : EuclideanSpace ℝ (OrderPairs P) | ∀ q, 0 ≤ c q} := by
      rw [himg_eq]; exact himg_closed.closure_eq
    rwa [hclo] at hmem
  
  obtain ⟨c, hc, hceq⟩ := hb_img
  simp only [Set.mem_setOf_eq] at hc
  refine ⟨fun q => c q, hc, ?_, ?_⟩
  · intro x
    have hxapp := congrArg (fun (v : EuclideanSpace ℝ (P ⊕ P)) => v (Sum.inl x)) hceq
    simp only at hxapp
    rw [margCLM_inl] at hxapp
    rw [hxapp, hbinl]
  · intro y
    have hyapp := congrArg (fun (v : EuclideanSpace ℝ (P ⊕ P)) => v (Sum.inr y)) hceq
    simp only at hyapp
    rw [margCLM_inr] at hyapp
    rw [hyapp, hbinr]

end Transport
end StatMech
