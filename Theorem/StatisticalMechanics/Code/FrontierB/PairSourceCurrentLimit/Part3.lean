/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/PairSourceCurrentLimit.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.PairSourceBoxCurrent.Part3
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxSpinLimit
import Theorem.StatisticalMechanics.Code.FrontierB.FreeBoxCurrentParity
import Theorem.StatisticalMechanics.Code.FrontierB.CurrentSelectionIndependence.Part3
import Def.StatisticalMechanics.Code.FrontierB.PairSourceCurrentLimit.Part3
open Filter MeasureTheory
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Ising Lattice


theorem growingPairSourceCurrentMeasure_edge_inverse_tail_le
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y)
    (k : ℕ) (e : Sym2 (Site d)) (K : ℕ) (hK : 0 < K) :
    (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k :
      Measure (InfiniteCurrentConfig (Sym2 (Site d))))
        {m | K ≤ m e} ≤
      ENNReal.ofReal
          (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy) / K := by
  let n := k + N
  let xn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite x (box_mono d (Nat.le_add_left N k) hx)
  let yn : StatMech.FK.boxVerts d n :=
    pairSourceBoxSite y (box_mono d (Nat.le_add_left N k) hy)
  let hxnyn : xn ≠ yn := pairSourceBoxSite_ne _ _ hxy
  let c := pairSourceBaseConstant d N beta x y hx hy
  have hc : 0 < c := pairSourceBaseConstant_pos d N beta hbeta x y hx hy
  by_cases he : e ∈ Set.range (boxCurrentEdgeIncl d n)
  · obtain ⟨eb, rfl⟩ := he
    have hcorr : c ≤ expectationJ (StatMech.FK.boxGraph d n) beta
        (fun _ => 1) {xn, yn} := by
      exact pairSourceBaseConstant_le_expectation d N n beta hbeta x y hx hy hxy
        (Nat.le_add_left N k)
    have htail := sourceCurrentMeasure_edge_inverse_tail_le
      (StatMech.FK.boxGraph d n) beta (fun _ => 1) hbeta.le
      (fun _ => by positivity) {xn, yn}
      (boxCurrentSum_pair_pos d n beta hbeta xn yn hxnyn) eb c hc hcorr K hK
    rw [show growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy k =
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


theorem growingPairSourceCurrentMeasure_subsequence
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu := by
  apply weakCurrent_subsequence_of_uniform_inverse_tail
    (growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy)
    (ENNReal.ofReal
      (Real.exp beta / pairSourceBaseConstant d N beta x y hx hy))
    ENNReal.ofReal_ne_top
  intro k e K hK
  exact growingPairSourceCurrentMeasure_edge_inverse_tail_le
    d N beta hbeta x y hx hy hxy k e K hK


theorem growingPairSourceCurrentMeasure_subsequence_with_cylinders
    (d N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (x y : Site d)
    (hx : x ∈ box d N) (hy : y ∈ box d N) (hxy : x ≠ y) :
    ∃ (nu : ProbabilityMeasure (InfiniteCurrentConfig (Sym2 (Site d))))
      (phi : ℕ → ℕ), StrictMono phi ∧
        WeakCurrentConverges
          ((growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy) ∘ phi) nu ∧
        ∀ (S : Finset (Sym2 (Site d))) (A : Set (↑S → ℕ)),
          Tendsto
            (fun k => growingPairSourceCurrentMeasure d N beta hbeta x y hx hy hxy
              (phi k) (currentCylinder S A)) atTop
            (nhds (nu (currentCylinder S A))) := by
  obtain ⟨nu, phi, hphi, hweak⟩ :=
    growingPairSourceCurrentMeasure_subsequence d N beta hbeta x y hx hy hxy
  exact ⟨nu, phi, hphi, hweak, hweak.cylinder⟩


end StatMech.FrontierB
