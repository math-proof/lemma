/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonCoarseTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.AllOpenCoarseProbability.Part2
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonFiniteMerge.Part2
import Theorem.StatisticalMechanics.Code.Walls.bkmmerge
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcation.Part2
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

open StatMech.Walls


theorem exists_siteThreeMeetBox_pos
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteThreeMeetBox n) := by
  have hcover : {eta : ConfigSpace (Site 2) |
      numInfiniteClusters 2 (siteToBond eta) = ⊤} ⊆
      ⋃ n, SiteThreeMeetBox n := by
    intro eta heta
    have hmem := iEqTop_subset_iUnion_threeMeetBox (d := 2) heta
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hmem
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  by_contra hcon
  simp only [not_exists, not_lt, nonpos_iff_eq_zero] at hcon
  have hunion0 : nu (⋃ n, SiteThreeMeetBox n) = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      nu (⋃ n, SiteThreeMeetBox n) ≤
          ∑' n, nu (SiteThreeMeetBox n) := measure_iUnion_le _
      _ = 0 := by simp [hcon]
  have hle :
      nu {eta : ConfigSpace (Site 2) |
          numInfiniteClusters 2 (siteToBond eta) = ⊤} ≤
        nu (⋃ n, SiteThreeMeetBox n) :=
    measure_mono hcover
  rw [hunion0] at hle
  exact (not_lt_of_ge hle) htop


theorem siteFaithfulAllOpenTrif_pos_of_top
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (htop : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤}) :
    ∃ n : ℕ, 0 < nu (SiteFaithfulAllOpenTrifAt n) := by
  obtain ⟨n, hnpos⟩ := exists_siteThreeMeetBox_pos nu htop
  refine ⟨n, positive_of_forceSitesOccupied_preimage
    nu epsilon hepsilon hinsert (boxFinsetBK 2 n)
      (measurableSet_siteFaithfulAllOpenTrifAt n) ?_ hnpos⟩
  intro eta heta
  exact siteForce_faithfulAllOpenTrif_of_threeMeetBox eta n heta


theorem siteFaithfulAllOpenTrif_prob_eq_zero
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu)
    (n : ℕ) :
    nu (SiteFaithfulAllOpenTrifAt n) = 0 := by
  let mu : Measure (ConfigSpace (Sym2 (Site 2))) := Measure.map siteToBond nu
  haveI : IsProbabilityMeasure mu :=
    inferInstance
  have hmuv : IsTranslationInvariant (G := Multiplicative (Site 2)) mu :=
    siteToBond_isTranslationInvariant nu hinv
  have hzero := faithfulAllOpenTrifAt_prob_eq_zero mu hmuv n
  rw [Measure.map_apply measurable_siteToBond
    (measurableSet_faithfulAllOpenTrifAt n 0)] at hzero
  exact hzero


theorem site_cluster_count_top_null_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (hinv : IsTranslationInvariant (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤} = 0 := by
  by_contra hne
  have hpos : 0 < nu {eta | numInfiniteClusters 2 (siteToBond eta) = ⊤} :=
    pos_iff_ne_zero.mpr hne
  obtain ⟨n, hnpos⟩ := siteFaithfulAllOpenTrif_pos_of_top
    nu epsilon hepsilon hinsert hpos
  rw [siteFaithfulAllOpenTrif_prob_eq_zero nu hinv n] at hnpos
  exact (lt_irrefl 0) hnpos


theorem site_cluster_count_ae_one_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon)
    (hperco : nu {eta | 1 ≤ numInfiniteClusters 2 (siteToBond eta)} = 1) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
  rcases site_cluster_count_ae_one_or_infinite
      nu herg epsilon hepsilon hinsert hperco with hone | htop
  · exact hone
  · rw [site_cluster_count_top_null_two nu herg.1 epsilon hepsilon hinsert] at htop
    exact False.elim (zero_ne_one htop)


theorem site_cluster_count_ae_zero_or_one_two
    (nu : Measure (ConfigSpace (Site 2))) [IsProbabilityMeasure nu]
    (herg : IsErgodic (G := Multiplicative (Site 2)) nu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasSiteInsertionLowerBound nu epsilon) :
    nu {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨
      nu {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
  obtain ⟨k, hk, hkCases⟩ := site_cluster_count_ae_lt_two_or_infinite
    nu herg epsilon hepsilon hinsert
  rcases hkCases with hk2 | hktop
  · have hkle : k ≤ 1 := enat_le_one_of_not_two hk2
    by_cases hkzero : k = 0
    · left
      rwa [hkzero] at hk
    · have hkone : k = 1 :=
        le_antisymm hkle (ENat.one_le_iff_ne_zero.mpr hkzero)
      right
      rwa [hkone] at hk
  · have htopzero := site_cluster_count_top_null_two
      nu herg.1 epsilon hepsilon hinsert
    rw [hktop, htopzero] at hk
    exact False.elim (zero_ne_one hk)


theorem interpolatedSite_cluster_count_ae_zero_or_one_two
    (T : MonotoneAutomaton 2) (mu : Measure (FieldTriple 2))
    [IsProbabilityMeasure mu]
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon) :
    (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters 2 (siteToBond eta) = 0} = 1 ∨
      (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters 2 (siteToBond eta) = 1} = 1 := by
  letI : IsProbabilityMeasure (interpolatedSiteLaw T mu) := by
    unfold interpolatedSiteLaw
    exact inferInstance
  exact site_cluster_count_ae_zero_or_one_two
    (interpolatedSiteLaw T mu)
    (interpolatedSiteLaw_isErgodic T mu herg)
    epsilon hepsilon
    (interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert)

end StatMech.FrontierA
