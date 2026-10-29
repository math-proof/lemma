/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionInfinite.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BKFirstExit
import Def.StatisticalMechanics.Code.Sharpness.TildeBc.Part9
import Theorem.StatisticalMechanics.Code.Percolation.DctDifferentialFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SubcriticalDecayFull.Part2
import Theorem.StatisticalMechanics.Code.Percolation.SharpnessUnconditional.Part2
import Theorem.StatisticalMechanics.Code.Lattice.JordanContour.Part3
import Def.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part3
open MeasureTheory Set Finset Filter
open scoped NNReal ENNReal BigOperators Topology


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

open StatMech.Lattice StatMech.Percolation

variable {d : ℕ}


theorem shk_pairSmul_injective (g : Multiplicative (Site d)) :
    Function.Injective (shk_pairSmul (d := d) g) := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [shk_pairSmul, Prod.mk.injEq] at h ⊢
  exact ⟨(MulAction.toPerm (β := Site d) g).injective h.1,
    (MulAction.toPerm (β := Site d) g).injective h.2⟩


theorem shk_boundaryEdges_translate (g : Multiplicative (Site d))
    (S : Finset (Site d)) :
    boundaryEdges d (shk_translateFinset g S) =
      (boundaryEdges d S).image (shk_pairSmul g) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqS, hqout, hqadj⟩ := shk_mem_boundaryEdges_iff.mp hq
    let a := g⁻¹ • q.1
    let b := g⁻¹ • q.2
    have hga : g • a = q.1 := by simp [a]
    have hgb : g • b = q.2 := by simp [b]
    have haS : a ∈ S := by
      apply (shk_mem_translateFinset_smul g S a).1
      simpa only [hga] using hqS
    have hbS : b ∉ S := by
      intro hb
      apply hqout
      have := (shk_mem_translateFinset_smul g S b).2 hb
      simpa only [hgb] using this
    have hab : (hypercubicLattice d).Adj a b := by
      apply (hyper_adj_smul g a b).1
      simpa only [hga, hgb] using hqadj
    rw [Finset.mem_image]
    refine ⟨(a, b), shk_mem_boundaryEdges_iff.mpr ⟨haS, hbS, hab⟩, ?_⟩
    simp only [shk_pairSmul, hga, hgb]
  · intro hq
    rw [Finset.mem_image] at hq
    obtain ⟨q0, hq0, rfl⟩ := hq
    obtain ⟨hqin, hqout, hqadj⟩ := shk_mem_boundaryEdges_iff.mp hq0
    apply shk_mem_boundaryEdges_iff.mpr
    exact ⟨(shk_mem_translateFinset_smul g S q0.1).2 hqin,
      fun h => hqout ((shk_mem_translateFinset_smul g S q0.2).1 h),
      (hyper_adj_smul g q0.1 q0.2).2 hqadj⟩


theorem shk_boundaryConnSum_translate (p : NNReal) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (h0 : origin d ∈ S) :
    ∑ q ∈ boundaryEdges d (shk_translateFinset g S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (shk_translateFinset g S : Set (Site d))
            (g • origin d) q.1) =
      ∑ q ∈ boundaryEdges d S, connWithinProb d p hp S q.1 := by
  classical
  rw [shk_boundaryEdges_translate, Finset.sum_image]
  apply Finset.sum_congr rfl
  intro q hq
  have hqS : q.1 ∈ S := (shk_mem_boundaryEdges_iff.mp hq).1
  have htrans := shk_connWithinEvent_prob_translate p hp g S
    (origin d) q.1 h0 hqS
  have hbook := connWithinProb_eq p hp S q.1 (by simpa using h0) (by simpa using hqS)
  simpa only [shk_pairSmul] using htrans.trans hbook.symm
  exact (shk_pairSmul_injective g).injOn


theorem shk_phi_translate (p : NNReal) (hp : p ≤ 1)
    (g : Multiplicative (Site d)) (S : Finset (Site d))
    (h0 : origin d ∈ S) :
    (p : ℝ) * ∑ q ∈ boundaryEdges d (shk_translateFinset g S),
        (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real
          (connWithinEvent d (shk_translateFinset g S : Set (Site d))
            (g • origin d) q.1) = phi d p hp S := by
  rw [shk_boundaryConnSum_translate p hp g S h0]
  rfl


end Sharpness
end StatMech
