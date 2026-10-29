/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3Bridge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonCoarseTrifurcationGeneral.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonSingleSiteStability.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.MultivaluedMap
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem one_le_numInfiniteClusters_siteToBond_iff
    (eta : ConfigSpace (Site d)) :
    1 ≤ numInfiniteClusters d (siteToBond eta) ↔
      ∃ x : Site d, (cluster d (siteToBond eta) x).Infinite := by
  unfold numInfiniteClusters
  rw [Set.one_le_encard_iff_nonempty]
  constructor
  · rintro ⟨C, hCinf, x, hCx⟩
    refine ⟨x, ?_⟩
    rw [← hCx]
    exact hCinf
  · rintro ⟨x, hx⟩
    exact ⟨cluster d (siteToBond eta) x, hx, x, rfl⟩


theorem one_le_numInfiniteClusters_siteToBond_mono
    {eta eta' : ConfigSpace (Site d)} (h : eta ≤ eta')
    (hperco : 1 ≤ numInfiniteClusters d (siteToBond eta)) :
    1 ≤ numInfiniteClusters d (siteToBond eta') := by
  rw [one_le_numInfiniteClusters_siteToBond_iff] at hperco ⊢
  obtain ⟨x, hx⟩ := hperco
  refine ⟨x, hx.mono ?_⟩
  intro y hy
  exact connected_mono (siteToBond_mono h) hy


theorem measurableSet_interpolatedSite_percolates
    (T : MonotoneAutomaton d) :
    MeasurableSet {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (interpolatedSite T q))} := by
  change MeasurableSet
    ((numInfiniteClusters d ∘ siteToBond ∘ interpolatedSite T) ⁻¹' Set.Ici 1)
  exact (measurable_numInfiniteClusters.comp
    (measurable_siteToBond.comp (measurable_interpolatedSite T)))
      MeasurableSet.of_discrete


theorem measurableSet_lowOutput_percolates
    (T : MonotoneAutomaton d) :
    MeasurableSet {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} := by
  change MeasurableSet
    ((numInfiniteClusters d ∘ siteToBond ∘ fun q : FieldTriple d => T q.1)
      ⁻¹' Set.Ici 1)
  exact (measurable_numInfiniteClusters.comp
    (measurable_siteToBond.comp (T.measurable_toFun.comp measurable_fst)))
      MeasurableSet.of_discrete


theorem interpolatedSite_percolates_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedSiteLaw T mu)
        {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)} = 1 := by
  have hsub : {q : FieldTriple d |
      1 ≤ numInfiniteClusters d (siteToBond (T q.1))} ⊆
      {q | 1 ≤ numInfiniteClusters d
        (siteToBond (interpolatedSite T q))} := by
    intro q hq
    exact one_le_numInfiniteClusters_siteToBond_mono
      (automatonLow_le_interpolated T q) hq
  have hfull : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (interpolatedSite T q))} = 1 := by
    apply le_antisymm prob_le_one
    exact hlow ▸ measure_mono hsub
  let B : Set (ConfigSpace (Site d)) :=
    {eta | 1 ≤ numInfiniteClusters d (siteToBond eta)}
  have hB : MeasurableSet B := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond) ⁻¹' Set.Ici 1)
    exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
      MeasurableSet.of_discrete
  change (interpolatedSiteLaw T mu) B = 1
  unfold interpolatedSiteLaw
  rw [Measure.map_apply (measurable_interpolatedSite T) hB]
  simpa [B] using hfull


theorem interpolatedSite_cluster_count_ae_one_of_lowOutput
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ENNReal) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1) :
    (interpolatedSiteLaw T mu)
        {eta | numInfiniteClusters d (siteToBond eta) = 1} = 1 := by
  letI : IsProbabilityMeasure (interpolatedSiteLaw T mu) := by
    unfold interpolatedSiteLaw
    exact inferInstance
  exact site_cluster_count_ae_one_general
    (interpolatedSiteLaw T mu) hd
    (interpolatedSiteLaw_isErgodic T mu herg)
    epsilon hepsilon
    (interpolatedSiteLaw_hasInsertionLowerBound T mu epsilon hinsert)
    (interpolatedSite_percolates_of_lowOutput T mu hlow)


end StatMech.FrontierA
