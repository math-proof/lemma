/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundary.Part3
import Theorem.StatisticalMechanics.Code.Walls.bdcdetcount.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls


theorem measurableSet_bgF2IndexAllOpen (L : ℕ) (j : Site 2) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        bgf2_IndexAllOpen omega L j} := by
  classical
  rw [show {omega : ConfigSpace (Sym2 (Site 2)) |
      bgf2_IndexAllOpen omega L j} =
      ⋂ x : Site 2, ⋂ y : Site 2,
        {omega | bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice 2).Adj x y → omega s(x, y) = true} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  by_cases hx : bgn_idx L x = j
  · by_cases hy : bgn_idx L y = j
    · by_cases hadj : (hypercubicLattice 2).Adj x y
      · simpa only [openSubgraph_adj, hx, hy, hadj, true_and,
          true_implies] using (measurableSet_openAdj x y)
      · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
            bgn_idx L x = j → bgn_idx L y = j →
              (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy, hadj,
            true_implies, false_implies]
        rw [heq]
        exact MeasurableSet.univ
    · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
          bgn_idx L x = j → bgn_idx L y = j →
            (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
        ext omega
        simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy,
          true_implies, false_implies]
      rw [heq]
      exact MeasurableSet.univ
  · have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
        bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice 2).Adj x y → omega s(x, y) = true} = Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, hx,
        false_implies]
    rw [heq]
    exact MeasurableSet.univ


theorem measurableSet_faithfulAllOpenTrifAt (L : ℕ) (j : Site 2) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        FaithfulAllOpenTrifAt omega L j} := by
  have hcoarse : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site 2)) |
        bc67_IsGnTrifurcation omega L (bgf2_centre L j)} := by
    have heq : {omega : ConfigSpace (Sym2 (Site 2)) |
        bc67_IsGnTrifurcation omega L (bgf2_centre L j)} =
        {omega | bc61_IsCoarseTrifurcation omega L (bgf2_centre L j)} := by
      ext omega
      exact (bc67_coarseTrif_is_G_n_trifurcation
        omega L (bgf2_centre L j)).symm
    rw [heq]
    exact bc62_measurableSet_coarseTrif L (bgf2_centre L j)
  exact hcoarse.inter (measurableSet_bgF2IndexAllOpen L j)


theorem bgf2_indexAllOpen_shift_centre
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) :
    let g : Multiplicative (Site 2) :=
      Multiplicative.ofAdd (bgf2_centre L j)
    bgf2_IndexAllOpen (shift g omega) L j ↔
      bgf2_IndexAllOpen omega L 0 := by
  let c := bgf2_centre L j
  let g : Multiplicative (Site 2) := Multiplicative.ofAdd c
  change bgf2_IndexAllOpen (shift g omega) L j ↔
    bgf2_IndexAllOpen omega L 0
  constructor
  · intro H x y hx hy hadj
    have hxc : bgn_idx L (x + c) = j := by
      rw [bdc_bgn_idx_shift L j x, hx, zero_add]
    have hyc : bgn_idx L (y + c) = j := by
      rw [bdc_bgn_idx_shift L j y, hy, zero_add]
    have hadjc : (hypercubicLattice 2).Adj (x + c) (y + c) :=
      (bdc_lat_shift c x y).2 hadj
    have hs := H (x + c) (y + c) hxc hyc hadjc
    have hex : g • x = x + c := by
      change c + x = x + c
      abel
    have hey : g • y = y + c := by
      change c + y = y + c
      abel
    have he := shift_apply_smul g omega x y
    rw [hex, hey] at he
    rwa [he] at hs
  · intro H x y hx hy hadj
    have hxs : bgn_idx L (x - c) = 0 := by
      have hkey := bdc_bgn_idx_shift L j (x - c)
      rw [sub_add_cancel, hx] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hys : bgn_idx L (y - c) = 0 := by
      have hkey := bdc_bgn_idx_shift L j (y - c)
      rw [sub_add_cancel, hy] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hadjs : (hypercubicLattice 2).Adj (x - c) (y - c) := by
      have hkey := bdc_lat_shift c (x - c) (y - c)
      rw [sub_add_cancel, sub_add_cancel] at hkey
      exact hkey.1 hadj
    have hopen := H (x - c) (y - c) hxs hys hadjs
    have hex : g • (x - c) = x := by
      change c + (x - c) = x
      abel
    have hey : g • (y - c) = y := by
      change c + (y - c) = y
      abel
    have he := shift_apply_smul g omega (x - c) (y - c)
    rw [hex, hey] at he
    rwa [he]


theorem faithfulAllOpenTrifAt_shift_centre
    (omega : ConfigSpace (Sym2 (Site 2))) (L : ℕ) (j : Site 2) :
    let g : Multiplicative (Site 2) :=
      Multiplicative.ofAdd (bgf2_centre L j)
    FaithfulAllOpenTrifAt (shift g omega) L j ↔
      FaithfulAllOpenTrifAt omega L 0 := by
  let g : Multiplicative (Site 2) :=
    Multiplicative.ofAdd (bgf2_centre L j)
  change FaithfulAllOpenTrifAt (shift g omega) L j ↔
    FaithfulAllOpenTrifAt omega L 0
  have hgc : g • (0 : Site 2) = bgf2_centre L j := by
    change bgf2_centre L j + 0 = bgf2_centre L j
    simp
  constructor
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation omega L 0 :=
      (bc62_isCoarseTrif_shift g omega L 0).1
        (by rw [hgc]; exact
          (bc67_coarseTrif_is_G_n_trifurcation
            (shift g omega) L (bgf2_centre L j)).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation omega L 0).1 hcoarse,
      (bgf2_indexAllOpen_shift_centre omega L j).1 hopen⟩
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation
        (shift g omega) L (bgf2_centre L j) := by
      rw [← hgc]
      exact (bc62_isCoarseTrif_shift g omega L 0).2
        ((bc67_coarseTrif_is_G_n_trifurcation omega L 0).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation
      (shift g omega) L (bgf2_centre L j)).1 hcoarse,
      (bgf2_indexAllOpen_shift_centre omega L j).2 hopen⟩


theorem faithfulAllOpenTrifAt_prob_const
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L : ℕ) (j : Site 2) :
    mu {omega | FaithfulAllOpenTrifAt omega L j} =
      mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
  let g : Multiplicative (Site 2) :=
    Multiplicative.ofAdd (bgf2_centre L j)
  have hpre : (shift g : ConfigSpace (Sym2 (Site 2)) →
      ConfigSpace (Sym2 (Site 2))) ⁻¹'
      {omega | FaithfulAllOpenTrifAt omega L j} =
      {omega | FaithfulAllOpenTrifAt omega L 0} := by
    ext omega
    exact faithfulAllOpenTrifAt_shift_centre omega L j
  calc
    mu {omega | FaithfulAllOpenTrifAt omega L j} =
        mu ((shift g) ⁻¹' {omega | FaithfulAllOpenTrifAt omega L j}) :=
      (hinv.measure_preimage g
        (measurableSet_faithfulAllOpenTrifAt L j)).symm
    _ = mu {omega | FaithfulAllOpenTrifAt omega L 0} := by rw [hpre]

lemma faithfulAllOpenTrifIndicesInBox_eq_sum_indicator
    (omega : ConfigSpace (Sym2 (Site 2))) (L N : ℕ) :
    ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) =
      ∑ j ∈ boxFinsetBK 2 N,
        ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
          (fun _ => (1 : ℝ≥0∞))) omega := by
  classical
  unfold faithfulAllOpenTrifIndicesInBox boxFinsetBK
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : FaithfulAllOpenTrifAt omega L j
  · simp [h]
  · simp [h]

theorem expected_faithfulAllOpenTrifIndicesInBox
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu)
    (L N : ℕ) :
    ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
      (boxFinsetBK 2 N).card •
        mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
  classical
  calc
    ∫⁻ omega,
        ((faithfulAllOpenTrifIndicesInBox omega L N).card : ℝ≥0∞) ∂mu =
        ∫⁻ omega, ∑ j ∈ boxFinsetBK 2 N,
          ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact faithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N
    _ = ∑ j ∈ boxFinsetBK 2 N, ∫⁻ omega,
          ({omega' | FaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ℝ≥0∞))) omega ∂mu := by
      rw [lintegral_finsetSum]
      intro j hj
      exact Measurable.indicator measurable_const
        (measurableSet_faithfulAllOpenTrifAt L j)
    _ = ∑ j ∈ boxFinsetBK 2 N,
          mu {omega | FaithfulAllOpenTrifAt omega L j} := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_indicator (measurableSet_faithfulAllOpenTrifAt L j)]
      simp
    _ = ∑ _j ∈ boxFinsetBK 2 N,
          mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
      apply Finset.sum_congr rfl
      intro j hj
      exact faithfulAllOpenTrifAt_prob_const mu hinv L j
    _ = (boxFinsetBK 2 N).card •
        mu {omega | FaithfulAllOpenTrifAt omega L 0} := by
      rw [Finset.sum_const]

end StatMech.FrontierA
