/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonFiniteMerge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonInsertion.Part3
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMergeGeom
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem exists_siteTwoMeetBox_pos
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    {k : ℕ∞} (hk2 : 2 ≤ k)
    (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) :
    ∃ n : ℕ, 0 < nu (SiteTwoMeetBox (d := d) n k) := by
  have hcover : {eta : ConfigSpace (Site d) |
      numInfiniteClusters d (siteToBond eta) = k} ⊆
      ⋃ n, SiteTwoMeetBox (d := d) n k := by
    intro eta heta
    have h := iEqLevel_subset_iUnion_twoMeetBox hk2 heta
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : nu (⋃ n, SiteTwoMeetBox (d := d) n k) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      nu (⋃ n, SiteTwoMeetBox (d := d) n k) ≤
          ∑' n, nu (SiteTwoMeetBox (d := d) n k) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle : nu {eta : ConfigSpace (Site d) |
      numInfiniteClusters d (siteToBond eta) = k} ≤
      nu (⋃ n, SiteTwoMeetBox (d := d) n k) := measure_mono hcover
  rw [hk, hunion0] at hle
  exact absurd hle (by norm_num)


theorem finite_constant_cluster_count_impossible
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    {k : ℕ∞} (hk2 : 2 ≤ k) (hktop : k ≠ ⊤)
    (hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1) : False := by
  obtain ⟨n, hnpos⟩ := exists_siteTwoMeetBox_pos nu hk2 hk
  let B : Set (ConfigSpace (Site d)) :=
    {eta | numInfiniteClusters d (siteToBond eta) < k}
  have hBmeas : MeasurableSet B := by
    exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
      (MeasurableSet.of_discrete)
  have hsub : SiteTwoMeetBox (d := d) n k ⊆
      (forceSitesOccupied (boxFinsetBK d n)) ⁻¹' B := by
    rintro eta ⟨hcount, x, y, hxbox, hybox, hx, hy, hne⟩
    change numInfiniteClusters d
      (siteToBond (forceSitesOccupied (boxFinsetBK d n) eta)) < k
    have hfin : numInfiniteClusters d (siteToBond eta) ≠ ⊤ := by
      rw [hcount]
      exact hktop
    have hlt := numInfiniteClusters_siteForce_lt_of_twoMeetBox n eta hfin
      hxbox hybox hx hy hne
    rwa [hcount] at hlt
  have hBpos : 0 < nu B := positive_of_forceSitesOccupied_preimage
    nu epsilon hepsilon hinsert (boxFinsetBK d n) hBmeas hsub hnpos
  have hBzero : nu B = 0 := by
    apply le_antisymm
    · have hlevelSub : {eta | numInfiniteClusters d (siteToBond eta) = k} ⊆ Bᶜ := by
        intro eta heta
        simp only [Set.mem_compl_iff]
        change ¬ numInfiniteClusters d (siteToBond eta) < k
        rw [heta]
        exact lt_irrefl k
      have hfull : nu Bᶜ = 1 := le_antisymm prob_le_one (hk ▸ measure_mono hlevelSub)
      exact (prob_compl_eq_one_iff hBmeas).mp hfull |>.le
    · exact bot_le
  rw [hBzero] at hBpos
  exact (lt_irrefl 0) hBpos


theorem site_cluster_count_ae_lt_two_or_infinite
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    ∃ k : ℕ∞,
      nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1 ∧
        (¬ 2 ≤ k ∨ k = ⊤) := by
  let mu : Measure (ConfigSpace (Sym2 (Site d))) := Measure.map siteToBond nu
  haveI : IsProbabilityMeasure mu :=
    inferInstance
  have hmuergo : IsErgodic (G := Multiplicative (Site d)) mu :=
    siteToBond_isErgodic nu herg
  obtain ⟨k, hkmu⟩ := numInfiniteClusters_ae_const mu hmuergo
  have hbondLevelMeas : MeasurableSet
      {omega : ConfigSpace (Sym2 (Site d)) | numInfiniteClusters d omega = k} := by
    change MeasurableSet ((numInfiniteClusters d) ⁻¹' ({k} : Set ℕ∞))
    exact measurable_numInfiniteClusters (MeasurableSet.of_discrete)
  have hk : nu {eta | numInfiniteClusters d (siteToBond eta) = k} = 1 := by
    change (Measure.map siteToBond nu)
      {omega | numInfiniteClusters d omega = k} = 1 at hkmu
    rw [Measure.map_apply measurable_siteToBond hbondLevelMeas] at hkmu
    exact hkmu
  refine ⟨k, hk, ?_⟩
  by_cases hk2 : 2 ≤ k
  · right
    by_contra hktop
    exact finite_constant_cluster_count_impossible nu epsilon hepsilon hinsert
      hk2 hktop hk
  · exact Or.inl hk2


theorem site_cluster_count_ae_one_or_infinite
    (nu : Measure (ConfigSpace (Site d))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site d)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (hperco : nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1) :
    nu {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 ∨
      nu {eta | numInfiniteClusters d (siteToBond eta) = ⊤} = 1 := by
  obtain ⟨k, hk, hkCases⟩ := site_cluster_count_ae_lt_two_or_infinite
    nu herg epsilon hepsilon hinsert
  rcases hkCases with hk2 | hktop
  · have hkle : k ≤ 1 := enat_le_one_of_not_two hk2
    have hkne : k ≠ 0 := by
      intro hkzero
      have hposMeas : MeasurableSet
          {eta : ConfigSpace (Site d) |
            1 ≤ numInfiniteClusters d (siteToBond eta)} := by
        change MeasurableSet
          ((numInfiniteClusters d ∘ siteToBond) ⁻¹' Set.Ici 1)
        exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
          (MeasurableSet.of_discrete)
      have hcomplZero : nu {eta : ConfigSpace (Site d) |
          1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ = 0 := by
        rw [measure_compl hposMeas (measure_ne_top nu _), hperco]
        simp
      have hsub : {eta : ConfigSpace (Site d) |
          numInfiniteClusters d (siteToBond eta) = k} ⊆
          {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ := by
        intro eta heta
        simp only [Set.mem_setOf_eq] at heta
        simp only [Set.mem_compl_iff, Set.mem_setOf_eq]
        intro hpos
        rw [heta, hkzero] at hpos
        norm_num at hpos
      have hle : nu {eta : ConfigSpace (Site d) |
          numInfiniteClusters d (siteToBond eta) = k} ≤
          nu {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}ᶜ :=
        measure_mono hsub
      rw [hk, hcomplZero] at hle
      exact one_ne_zero (le_antisymm hle bot_le)
    have hkone : k = 1 := le_antisymm hkle (ENat.one_le_iff_ne_zero.mpr hkne)
    left
    rwa [hkone] at hk
  · right
    rwa [hktop] at hk

end StatMech.FrontierA
