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
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3Bridge.Part3
open MeasureTheory Set
open scoped ENNReal


namespace StatMech.FrontierA

open StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Percolation

variable {d : ℕ}


theorem measurableSet_pairHighCluster_meets_lowInfinite (x : Site d) :
    MeasurableSet {omega : PairSiteConfig d |
      (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty} := by
  have heq : {omega : PairSiteConfig d |
      (pairHighCluster omega x ∩ pairLowInfiniteVertices omega).Nonempty} =
      ⋃ y : Site d, {omega | y ∈ pairHighCluster omega x} ∩
        {omega | y ∈ pairLowInfiniteVertices omega} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact Set.nonempty_def
  rw [heq]
  exact MeasurableSet.iUnion fun y =>
    (measurableSet_pairHighConnected x y).inter
      (measurableSet_pairLowInfinite y)


theorem measurableSet_pairHighClusterAbsorption :
    MeasurableSet {omega : PairSiteConfig d |
      PairHighClusterAbsorption omega} := by
  have heq : {omega : PairSiteConfig d | PairHighClusterAbsorption omega} =
      ⋂ x : Site d,
        {omega | ¬(pairHighCluster omega x).Infinite} ∪
          {omega | (pairHighCluster omega x ∩
            pairLowInfiniteVertices omega).Nonempty} := by
    ext omega
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_union]
    constructor
    · intro h x
      by_cases hx : (pairHighCluster omega x).Infinite
      · exact Or.inr (h x hx)
      · exact Or.inl hx
    · intro h x hx
      rcases h x with hnot | hmeet
      · exact (hnot hx).elim
      · exact hmeet
  rw [heq]
  exact MeasurableSet.iInter fun x =>
    (measurableSet_pairHighInfinite x).compl.union
      (measurableSet_pairHighCluster_meets_lowInfinite x)


theorem high_cluster_count_le_one_of_low_unique_of_absorption
    (omega : PairSiteConfig d)
    (hlow : numInfiniteClusters d
      (siteToBond (pairSiteLeft omega)) = 1)
    (hnested : pairSiteLeft omega ≤ pairSiteRight omega)
    (habsorb : PairHighClusterAbsorption omega) :
    numInfiniteClusters d (siteToBond (pairSiteRight omega)) ≤ 1 := by
  unfold numInfiniteClusters at hlow ⊢
  rw [Set.encard_le_one_iff_subsingleton]
  intro C hC D hD
  obtain ⟨hCinf, x, rfl⟩ := hC
  obtain ⟨hDinf, y, rfl⟩ := hD
  obtain ⟨a, hax, halow⟩ := habsorb x hCinf
  obtain ⟨b, hby, hblow⟩ := habsorb y hDinf
  have hlowSub : (infiniteClusters d
      (siteToBond (pairSiteLeft omega))).Subsingleton := by
    rw [← Set.encard_le_one_iff_subsingleton, hlow]
  have habClusters : cluster d (siteToBond (pairSiteLeft omega)) a =
      cluster d (siteToBond (pairSiteLeft omega)) b := by
    apply hlowSub
    · exact ⟨halow, a, rfl⟩
    · exact ⟨hblow, b, rfl⟩
  have habLow : Connected d (siteToBond (pairSiteLeft omega)) a b := by
    apply mem_cluster.mp
    rw [habClusters]
    exact self_mem_cluster _ b
  have habHigh : Connected d (siteToBond (pairSiteRight omega)) a b :=
    connected_mono (siteToBond_mono hnested) habLow
  have hxy : Connected d (siteToBond (pairSiteRight omega)) x y :=
    hax.trans (habHigh.trans hby.symm)
  exact cluster_eq_of_connected hxy


theorem highOutput_cluster_count_ae_le_one_of_absorption
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ENNReal) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
    (habsorb : ∀ᵐ q ∂mu,
      PairHighClusterAbsorption (interpolatedHighPair T q)) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
  have hauxLaw := interpolatedSite_cluster_count_ae_one_of_lowOutput
    T mu hd herg epsilon hepsilon hinsert hlow
  have hauxMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘ interpolatedSite T) ⁻¹' {1})
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp (measurable_interpolatedSite T)))
        MeasurableSet.of_discrete
  have hauxField : mu {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1} = 1 := by
    let B : Set (ConfigSpace (Site d)) :=
      {eta | numInfiniteClusters d (siteToBond eta) = 1}
    have hB : MeasurableSet B := by
      change MeasurableSet
        ((numInfiniteClusters d ∘ siteToBond) ⁻¹' ({1} : Set ℕ∞))
      exact (measurable_numInfiniteClusters.comp measurable_siteToBond)
        MeasurableSet.of_discrete
    change (interpolatedSiteLaw T mu) B = 1 at hauxLaw
    unfold interpolatedSiteLaw at hauxLaw
    rw [Measure.map_apply (measurable_interpolatedSite T) hB] at hauxLaw
    simpa [B] using hauxLaw
  have hauxAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (interpolatedSite T q)) = 1 := by
    apply (ae_iff_measure_eq hauxMeas.nullMeasurableSet).2
    simpa using hauxField
  have hresultAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1 := by
    filter_upwards [hauxAE, hmono, habsorb] with q hunique hqmono hqabsorb
    exact high_cluster_count_le_one_of_low_unique_of_absorption
      (interpolatedHighPair T q) hunique
      (interpolatedHighPair_nested T q hqmono) hqabsorb
  have hresultMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' Set.Iic 1)
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  have := (ae_iff_measure_eq hresultMeas.nullMeasurableSet).1 hresultAE
  simpa using this


theorem highOutput_cluster_count_ae_one_of_absorption
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d)
    (herg : IsTripleFieldErgodic mu)
    (epsilon : ENNReal) (hepsilon : epsilon ≠ 0)
    (hinsert : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d (siteToBond (T q.1))} = 1)
    (habsorb : ∀ᵐ q ∂mu,
      PairHighClusterAbsorption (interpolatedHighPair T q)) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) = 1} = 1 := by
  have hleFull := highOutput_cluster_count_ae_le_one_of_absorption
    T mu hd herg epsilon hepsilon hinsert hmono hlow habsorb
  have hlowAE : ∀ᵐ q ∂mu,
      1 ≤ numInfiniteClusters d (siteToBond (T q.1)) := by
    apply (ae_iff_measure_eq
      (measurableSet_lowOutput_percolates T).nullMeasurableSet).2
    simpa using hlow
  have hleMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' Set.Iic 1)
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  have hleAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1 := by
    apply (ae_iff_measure_eq hleMeas.nullMeasurableSet).2
    simpa using hleFull
  have honeAE : ∀ᵐ q ∂mu,
      numInfiniteClusters d (siteToBond (T q.2.2)) = 1 := by
    filter_upwards [hlowAE, hmono, hleAE] with q hqLow hqMono hqLe
    apply le_antisymm hqLe
    exact one_le_numInfiniteClusters_siteToBond_mono
      (T.monotone (hqMono.1.trans hqMono.2)) hqLow
  have honeMeas : MeasurableSet {q : FieldTriple d |
      numInfiniteClusters d (siteToBond (T q.2.2)) = 1} := by
    change MeasurableSet
      ((numInfiniteClusters d ∘ siteToBond ∘
        fun q : FieldTriple d => T q.2.2) ⁻¹' {1})
    exact (measurable_numInfiniteClusters.comp
      (measurable_siteToBond.comp
        (T.measurable_toFun.comp measurable_snd.snd)))
          MeasurableSet.of_discrete
  calc
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) = 1} = mu Set.univ :=
      (ae_iff_measure_eq honeMeas.nullMeasurableSet).1 honeAE
    _ = 1 := measure_univ

end StatMech.FrontierA
