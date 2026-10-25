/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PlusFreeSourceJointLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PlusPairSourceCurrentLimit
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Def.StatisticalMechanics.Code.FrontierB.PlusFreeSourceJointLimit
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem growingFreePairSourceCurrentMeasure_edge_inverse_tail_le
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (growingFreePairSourceCurrentMeasure
      d N beta hbeta x y hx hy hxy k :
        Measure (InfiniteCurrentConfig (Sym2 (Site d)))) {m | K ≤ m e} ≤
      ENNReal.ofReal
          (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
  let n := (k + N) + 1
  let hNn : N ≤ n := le_trans (Nat.le_add_left N k) (Nat.le_succ _)
  let xn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite x (box_mono d hNn hx)
  let yn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite y (box_mono d hNn hy)
  let hxnyn : xn ≠ yn := pairSourceBoxSite_ne _ _ hxy
  let c := pairSourceBaseConstant d N beta x y hx hy
  have hc : 0 < c := pairSourceBaseConstant_pos d N beta hbeta x y hx hy
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨eb, rfl⟩ := he
    have hcorr : c ≤ expectationJ (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) {xn, yn} :=
      pairSourceBaseConstant_le_expectation
        d N n beta hbeta x y hx hy hxy hNn
    have htail := sourceCurrentMeasure_edge_inverse_tail_le
      (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {xn, yn}
      (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) eb c hc hcorr K hK
    rw [show growingFreePairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy k =
      pairSourceBoxCurrentMeasure d n beta hbeta xn yn hxnyn by rfl,
      pairSourceBoxCurrentMeasure_edge_tail]
    calc
      (sourceCurrentMeasure (StatMech.FK.boxGraph d n) beta
          (fun _ => 1) hbeta.le (fun _ => by positivity) {xn, yn}
          (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) :
            Measure (EdgeCurrent (StatMech.FK.boxGraph d n))) {m | K ≤ m eb} ≤
          ENNReal.ofReal (Real.exp beta / (c * K)) := by simpa using htail
      _ = ENNReal.ofReal (Real.exp beta / c) / K := by
        rw [← ENNReal.ofReal_natCast K,
          ← ENNReal.ofReal_div_of_pos (show (0 : ℝ) < K by exact_mod_cast hK)]
        congr 1
        simp only [div_eq_mul_inv, mul_inv]
        ring
  · change Measure.map (extendBoxCurrent d n) _ {m | K ≤ m e} ≤ _
    have hset : MeasurableSet
        {m : InfiniteCurrentConfig (Sym2 (Site d)) | K ≤ m e} :=
      (measurable_pi_apply e) MeasurableSet.of_discrete
    rw [Measure.map_apply (measurable_extendBoxCurrent d n) hset]
    have hpre : extendBoxCurrent d n ⁻¹' {m | K ≤ m e} = ∅ := by
      ext m
      simp [extendBoxCurrent_outside d n m e he, Nat.not_le_of_gt hK]
    rw [hpre]
    simp


theorem plusFreeSourceCurrentMeasure_joint_subsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nuFree nuPlus : ProbabilityMeasure
        (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingFreePairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nuFree ∧
        WeakCurrentConverges
          ((growingPlusPairSourceCurrentMeasure
            d N beta hbeta x y hx hy hxy) ∘ phi) nuPlus := by
  obtain ⟨nuFree, phiFree, hphiFree, hfree⟩ :=
    weakCurrent_subsequence_of_uniform_inverse_tail
      (growingFreePairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
      (ENNReal.ofReal
        (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy))
      ENNReal.ofReal_ne_top
      (growingFreePairSourceCurrentMeasure_edge_inverse_tail_le
        d N beta hbeta x y hx hy hxy)
  obtain ⟨nuPlus, phiPlus, hphiPlus, hplus⟩ :=
    weakCurrent_subsequence_of_uniform_inverse_tail
      ((growingPlusPairSourceCurrentMeasure
        d N beta hbeta x y hx hy hxy) ∘ phiFree)
      (ENNReal.ofReal (2 * Real.exp beta)) ENNReal.ofReal_ne_top
      (fun i e K hK =>
        growingPlusPairSourceCurrentMeasure_edge_inverse_tail_le
          d N beta hbeta x y hx hy hxy (phiFree i) e K hK)
  refine ⟨nuFree, nuPlus, phiFree ∘ phiPlus,
    hphiFree.comp hphiPlus, ?_, hplus⟩
  exact hfree.comp hphiPlus.tendsto_atTop


end StatMech.FrontierB
