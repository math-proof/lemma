/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AllOpenCoarseProbabilityGeneral.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseBoundaryGeneral.Part2
import Theorem.StatisticalMechanics.Code.Percolation.CanonBurtonKeane
import Theorem.StatisticalMechanics.Code.Walls.bc62coarseclose.Part2
open Finset Set SimpleGraph MeasureTheory Filter Topology
open scoped ENNReal BigOperators


namespace StatMech.FrontierA

open StatMech StatMech.ConfigSpace StatMech.Lattice StatMech.Percolation

open StatMech.Walls

variable {d : ℕ}


theorem measurableSet_bgfdIndexAllOpen (L : ℕ) (j : Site d) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        BgfdIndexAllOpen omega L j} := by
  classical
  rw [show {omega : ConfigSpace (Sym2 (Site d)) |
      BgfdIndexAllOpen omega L j} =
      ⋂ x : Site d, ⋂ y : Site d,
        {omega | bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice d).Adj x y → omega s(x, y) = true} by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rfl]
  refine MeasurableSet.iInter fun x => MeasurableSet.iInter fun y => ?_
  by_cases hx : bgn_idx L x = j
  · by_cases hy : bgn_idx L y = j
    · by_cases hadj : (hypercubicLattice d).Adj x y
      · simpa only [openSubgraph_adj, hx, hy, hadj, true_and,
          true_implies] using (measurableSet_openAdj x y)
      · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
            bgn_idx L x = j → bgn_idx L y = j →
              (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
            Set.univ := by
          ext omega
          simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy, hadj,
            true_implies, false_implies]
        rw [heq]
        exact MeasurableSet.univ
    · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
          bgn_idx L x = j → bgn_idx L y = j →
            (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
          Set.univ := by
        ext omega
        simp only [Set.mem_setOf_eq, Set.mem_univ, hx, hy,
          true_implies, false_implies]
      rw [heq]
      exact MeasurableSet.univ
  · have heq : {omega : ConfigSpace (Sym2 (Site d)) |
        bgn_idx L x = j → bgn_idx L y = j →
          (hypercubicLattice d).Adj x y → omega s(x, y) = true} =
        Set.univ := by
      ext omega
      simp only [Set.mem_setOf_eq, Set.mem_univ, hx, false_implies]
    rw [heq]
    exact MeasurableSet.univ


theorem measurableSet_bgfdFaithfulAllOpenTrifAt (L : ℕ) (j : Site d) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        BgfdFaithfulAllOpenTrifAt omega L j} := by
  have hcoarse : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) |
        bc67_IsGnTrifurcation omega L (bgfdCentre L j)} := by
    have heq : {omega : ConfigSpace (Sym2 (Site d)) |
        bc67_IsGnTrifurcation omega L (bgfdCentre L j)} =
        {omega | bc61_IsCoarseTrifurcation omega L (bgfdCentre L j)} := by
      ext omega
      exact (bc67_coarseTrif_is_G_n_trifurcation
        omega L (bgfdCentre L j)).symm
    rw [heq]
    exact bc62_measurableSet_coarseTrif L (bgfdCentre L j)
  exact hcoarse.inter (measurableSet_bgfdIndexAllOpen L j)


theorem bgfd_indexAllOpen_shift_centre
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) :
    let g : Multiplicative (Site d) :=
      Multiplicative.ofAdd (bgfdCentre L j)
    BgfdIndexAllOpen (shift g omega) L j ↔
      BgfdIndexAllOpen omega L 0 := by
  let c := bgfdCentre L j
  let g : Multiplicative (Site d) := Multiplicative.ofAdd c
  change BgfdIndexAllOpen (shift g omega) L j ↔
    BgfdIndexAllOpen omega L 0
  constructor
  · intro H x y hx hy hadj
    have hxc : bgn_idx L (x + c) = j := by
      rw [bgfd_idx_shift L j x, hx, zero_add]
    have hyc : bgn_idx L (y + c) = j := by
      rw [bgfd_idx_shift L j y, hy, zero_add]
    have hadjc : (hypercubicLattice d).Adj (x + c) (y + c) :=
      (bgfd_lat_shift c x y).2 hadj
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
      have hkey := bgfd_idx_shift L j (x - c)
      rw [sub_add_cancel, hx] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hys : bgn_idx L (y - c) = 0 := by
      have hkey := bgfd_idx_shift L j (y - c)
      rw [sub_add_cancel, hy] at hkey
      apply add_right_cancel (b := j)
      simpa using hkey.symm
    have hadjs : (hypercubicLattice d).Adj (x - c) (y - c) := by
      have hkey := bgfd_lat_shift c (x - c) (y - c)
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


theorem bgfdFaithfulAllOpenTrifAt_shift_centre
    (omega : ConfigSpace (Sym2 (Site d))) (L : ℕ) (j : Site d) :
    let g : Multiplicative (Site d) :=
      Multiplicative.ofAdd (bgfdCentre L j)
    BgfdFaithfulAllOpenTrifAt (shift g omega) L j ↔
      BgfdFaithfulAllOpenTrifAt omega L 0 := by
  let g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (bgfdCentre L j)
  change BgfdFaithfulAllOpenTrifAt (shift g omega) L j ↔
    BgfdFaithfulAllOpenTrifAt omega L 0
  have hgc : g • (0 : Site d) = bgfdCentre L j := by
    change bgfdCentre L j + 0 = bgfdCentre L j
    simp
  constructor
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation omega L 0 :=
      (bc62_isCoarseTrif_shift g omega L 0).1
        (by rw [hgc]; exact
          (bc67_coarseTrif_is_G_n_trifurcation
            (shift g omega) L (bgfdCentre L j)).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation omega L 0).1 hcoarse,
      (bgfd_indexAllOpen_shift_centre omega L j).1 hopen⟩
  · rintro ⟨htri, hopen⟩
    have hcoarse : bc61_IsCoarseTrifurcation
        (shift g omega) L (bgfdCentre L j) := by
      rw [← hgc]
      exact (bc62_isCoarseTrif_shift g omega L 0).2
        ((bc67_coarseTrif_is_G_n_trifurcation omega L 0).2 htri)
    exact ⟨(bc67_coarseTrif_is_G_n_trifurcation
      (shift g omega) L (bgfdCentre L j)).1 hcoarse,
      (bgfd_indexAllOpen_shift_centre omega L j).2 hopen⟩


theorem bgfdFaithfulAllOpenTrifAt_prob_const
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L : ℕ) (j : Site d) :
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
      mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
  let g : Multiplicative (Site d) :=
    Multiplicative.ofAdd (bgfdCentre L j)
  have hpre : (shift g : ConfigSpace (Sym2 (Site d)) →
      ConfigSpace (Sym2 (Site d))) ⁻¹'
      {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
      {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
    ext omega
    exact bgfdFaithfulAllOpenTrifAt_shift_centre omega L j
  calc
    mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} =
        mu ((shift g) ⁻¹' {omega |
          BgfdFaithfulAllOpenTrifAt omega L j}) :=
      (hinv.measure_preimage g
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)).symm
    _ = mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by rw [hpre]

lemma bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator
    (omega : ConfigSpace (Sym2 (Site d))) (L N : ℕ) :
    ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ENNReal) =
      ∑ j ∈ boxFinsetBK d N,
        ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
          (fun _ => (1 : ENNReal))) omega := by
  classical
  unfold bgfdFaithfulAllOpenTrifIndicesInBox boxFinsetBK
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : BgfdFaithfulAllOpenTrifAt omega L j
  · simp [h]
  · simp [h]

theorem expected_bgfdFaithfulAllOpenTrifIndicesInBox
    (mu : Measure (ConfigSpace (Sym2 (Site d))))
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) mu)
    (L N : ℕ) :
    ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ENNReal) ∂mu =
      (boxFinsetBK d N).card •
        mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
  classical
  calc
    ∫⁻ omega,
        ((bgfdFaithfulAllOpenTrifIndicesInBox omega L N).card : ENNReal) ∂mu =
        ∫⁻ omega, ∑ j ∈ boxFinsetBK d N,
          ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ENNReal))) omega ∂mu := by
      apply lintegral_congr
      intro omega
      exact bgfdFaithfulAllOpenTrifIndicesInBox_eq_sum_indicator omega L N
    _ = ∑ j ∈ boxFinsetBK d N, ∫⁻ omega,
          ({omega' | BgfdFaithfulAllOpenTrifAt omega' L j}.indicator
            (fun _ => (1 : ENNReal))) omega ∂mu := by
      rw [lintegral_finsetSum]
      intro j hj
      exact Measurable.indicator measurable_const
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)
    _ = ∑ j ∈ boxFinsetBK d N,
          mu {omega | BgfdFaithfulAllOpenTrifAt omega L j} := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [lintegral_indicator
        (measurableSet_bgfdFaithfulAllOpenTrifAt L j)]
      simp
    _ = ∑ _j ∈ boxFinsetBK d N,
          mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
      apply Finset.sum_congr rfl
      intro j hj
      exact bgfdFaithfulAllOpenTrifAt_prob_const mu hinv L j
    _ = (boxFinsetBK d N).card •
        mu {omega | BgfdFaithfulAllOpenTrifAt omega L 0} := by
      rw [Finset.sum_const]

end StatMech.FrontierA
