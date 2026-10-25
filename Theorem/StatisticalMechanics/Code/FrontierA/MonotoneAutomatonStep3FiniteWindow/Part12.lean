/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonStep3FiniteWindow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonAbsorptionReduction.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteEventMultivalued
import Theorem.StatisticalMechanics.Code.Lattice.SegmentConn
import Theorem.StatisticalMechanics.Code.Percolation.GridBoxConnected.Part2
import Def.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonStep3FiniteWindow.Part11
open MeasureTheory Set Finset SimpleGraph
open scoped ENNReal NNReal BigOperators


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem step3WindowMask_subset_box (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) :
    step3WindowMask T D N q ⊆ boxFinsetBK d N := by
  classical
  intro z hz
  exact (Finset.mem_filter.mp hz).1

theorem step3WindowMask_matches (T : MonotoneAutomaton d)
    (D N : ℕ) (q : FieldTriple d) :
    step3MaskMatches T D N (step3WindowMask T D N q) q := by
  classical
  intro z
  rw [step3WindowMask, Finset.mem_filter]
  simp only [pairLowInfiniteVertices_zeroHighPair]

theorem coordinateBetween_mem_box {x y z : Site d} {N : ℕ}
    (hx : x ∈ box d N) (hy : y ∈ box d N)
    (hz : z ∈ coordinateBetween x y) : z ∈ box d N := by
  intro k
  have hxk := hx k
  have hyk := hy k
  have hzk := hz k
  rcases le_total (x k) (y k) with hxy | hyx
  · simp only [min_eq_left hxy, max_eq_right hxy] at hzk
    push_cast at hxk hyk ⊢
    omega
  · simp only [min_eq_right hyx, max_eq_left hyx] at hzk
    push_cast at hxk hyk ⊢
    omega

theorem pairHighCluster_interpolatedHighPair_eq_siteCluster
    (T : MonotoneAutomaton d) (q : FieldTriple d) (x : Site d) :
    pairHighCluster (interpolatedHighPair T q) x = siteCluster (T q.2.2) x := by
  ext z
  exact connected_siteToBond_iff _ _ _

theorem step3Contact_forceSet_subset_mask
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    {x y : Site d}
    (hxBox : x ∈ boxFinsetBK d N) (hyBox : y ∈ boxFinsetBK d N)
    (hxLow : x ∈ pairLowInfiniteVertices (interpolatedHighPair T q))
    (hxy : l1dist d x y = D) :
    contactForceSet x y ⊆ step3WindowMask T D N q := by
  classical
  intro z hz
  rw [step3WindowMask, Finset.mem_filter]
  have hzBetween := (mem_contactForceSet.mp hz).1
  have hzne := (mem_contactForceSet.mp hz).2
  have hzLe : l1dist d x z ≤ D :=
    (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
  have hzLt : l1dist d x z < D := by
    exact lt_of_le_of_ne hzLe (fun heq => hzne
      (eq_right_of_mem_coordinateBetween_of_l1dist_eq hzBetween
        (heq.trans hxy.symm)))
  have hx' := mem_boxFinsetBK_iff.mp hxBox
  have hy' := mem_boxFinsetBK_iff.mp hyBox
  exact ⟨mem_boxFinsetBK_iff.mpr (coordinateBetween_mem_box hx' hy' hzBetween),
    x, hxLow, hzLt⟩

theorem contactForceSet_l1dist_lt {x y z : Site d} {D : ℕ}
    (hxy : l1dist d x y = D) (hz : z ∈ contactForceSet x y) :
    l1dist d x z < D := by
  have hzBetween := (mem_contactForceSet.mp hz).1
  have hzne := (mem_contactForceSet.mp hz).2
  have hzLe : l1dist d x z ≤ D :=
    (coordinateBetween_l1dist_le hzBetween).trans_eq hxy
  exact lt_of_le_of_ne hzLe (fun heq => hzne
    (eq_right_of_mem_coordinateBetween_of_l1dist_eq hzBetween
      (heq.trans hxy.symm)))

theorem step3Deletion_cluster_eq_original
    (T : MonotoneAutomaton d) (D : ℕ) (q : FieldTriple d)
    (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
    (S : Finset (Site d))
    (hnear : ∀ z ∈ S, ∃ x ∈
      pairLowInfiniteVertices (interpolatedHighPair T q), l1dist d x z < D) :
    pairHighCluster (zeroHighPair T S q) 0 =
      pairHighCluster (interpolatedHighPair T q) 0 := by
  have hinfPair :
      (pairHighCluster (interpolatedHighPair T q) 0).Infinite :=
    hD.1.1.1.1
  have hinfSite : (siteCluster (T q.2.2) 0).Infinite := by
    rw [← pairHighCluster_interpolatedHighPair_eq_siteCluster]
    exact hinfPair
  have havoid : ∀ z ∈ S, z ∉ siteCluster (T q.2.2) 0 := by
    intro z hzS hzCluster
    obtain ⟨x, hxLow, hxz⟩ := hnear z hzS
    have hzPair : z ∈ pairHighCluster (interpolatedHighPair T q) 0 := by
      rw [pairHighCluster_interpolatedHighPair_eq_siteCluster]
      exact hzCluster
    have hlower := hD.1.2 z hzPair x hxLow
    exact (Nat.not_lt_of_ge hlower) (by simpa [l1dist_comm] using hxz)
  rw [pairHighCluster_zeroHighPair_eq_siteCluster,
    pairHighCluster_interpolatedHighPair_eq_siteCluster]
  exact siteCluster_zeroFields_eq_of_final_infinite_of_avoids
    T q.2.2 S 0 hinfSite havoid

theorem step3Contact_gives_source
    (T : MonotoneAutomaton d) (D N : ℕ) (q : FieldTriple d)
    (hD : interpolatedHighPair T q ∈ pairStep3DistanceAt (0 : Site d) D)
    {x y : Site d}
    (hcontact : (x, y) ∈ step3WindowContacts T D N q) :
    q ∈ step3SourceEvent T D N
      ((step3WindowMask T D N q, x), y) := by
  classical
  have hcontact' := Finset.mem_filter.mp hcontact
  have hboxes := Finset.mem_product.mp hcontact'.1
  rcases hcontact'.2 with ⟨hxLow, hyNearest, hxy⟩
  have hforceSub := step3Contact_forceSet_subset_mask T D N q
    hboxes.1 hboxes.2 hxLow hxy
  have hbaseEq := step3Deletion_cluster_eq_original T D q hD
    (step3WindowMask T D N q) (by
      intro z hz
      exact (Finset.mem_filter.mp hz).2)
  have hforceEq := step3Deletion_cluster_eq_original T D q hD
    (contactForceSet x y) (by
      intro z hz
      exact ⟨x, hxLow, contactForceSet_l1dist_lt hxy hz⟩)
  have hyOriginal : y ∈ pairHighCluster (interpolatedHighPair T q) 0 :=
    pairNearestHighSet_subset_cluster _ _ hyNearest
  have hforceDisjoint : zeroHighPair T (contactForceSet x y) q ∈
      pairDisjointInfiniteHighAt (0 : Site d) := by
    constructor
    · rw [hforceEq]
      exact hD.1.1.1.1
    · rw [hforceEq]
      simpa only [pairLowInfiniteVertices_zeroHighPair] using hD.1.1.1.2
  refine ⟨step3WindowMask_matches T D N q, hforceSub, hxy,
    ?_, ?_, hforceDisjoint, ?_⟩
  · simpa only [pairLowInfiniteVertices_zeroHighPair] using hxLow
  · rw [hbaseEq]
    exact hyOriginal
  · exact hforceEq.trans hbaseEq.symm

theorem step3CoreWindow_sourceDegree
    (T : MonotoneAutomaton d) (D N K : ℕ) (q : FieldTriple d)
    (hq : q ∈ step3CoreWindowEvent T D N K) :
    K ≤ finiteEventMultiplicity (step3Indices (d := d) N)
      (step3SourceEvent T D N) q := by
  classical
  let C := step3WindowContacts T D N q
  let M := step3WindowMask T D N q
  have hcard : K ≤ C.card := hq.2
  apply hcard.trans
  unfold finiteEventMultiplicity
  apply Finset.card_le_card_of_injOn
    (fun p : Site d × Site d => ((M, p.1), p.2))
  · intro p hp
    have hpC : p ∈ step3WindowContacts T D N q := hp
    have hp' := Finset.mem_filter.mp hpC
    have hpBoxes := Finset.mem_product.mp hp'.1
    apply Finset.mem_filter.mpr
    constructor
    · rw [step3Indices]
      apply Finset.mem_product.mpr
      constructor
      · apply Finset.mem_product.mpr
        exact ⟨Finset.mem_powerset.mpr (step3WindowMask_subset_box T D N q),
          hpBoxes.1⟩
      · exact hpBoxes.2
    · exact step3Contact_gives_source T D N q hq.1 hpC
  · intro p hp r hr heq
    exact Prod.ext (congrArg (fun i => i.1.2) heq)
      (congrArg (fun i => i.2) heq)


theorem step3CoreWindow_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D N K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    epsilon ^ (boxFinsetBK d D).card * K *
        mu (step3CoreWindowEvent T D N K) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  apply step3FiniteWindow_probability_bound T mu D N K epsilon hinsert
    (step3CoreWindowEvent T D N K)
    (measurableSet_step3CoreWindowEvent T D N K)
  intro q hq
  exact step3CoreWindow_sourceDegree T D N K q hq

theorem step3Distance_probability_bound
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D K : ℕ) (epsilon : ℝ≥0∞)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    epsilon ^ (boxFinsetBK d D).card * K *
        mu ((interpolatedHighPair T) ⁻¹'
          pairStep3DistanceAt (0 : Site d) D) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
  let c : ℝ≥0∞ := epsilon ^ (boxFinsetBK d D).card * K
  have hmono := step3CoreWindowEvent_mono T D K
  have hN : ∀ N, c * mu (step3CoreWindowEvent T D N K) ≤
      (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞) := by
    intro N
    exact step3CoreWindow_probability_bound T mu D N K epsilon hinsert
  rw [step3Distance_preimage_eq_iUnion_windows T D K,
    hmono.measure_iUnion]
  change c * (⨆ N, mu (step3CoreWindowEvent T D N K)) ≤ _
  rw [ENNReal.mul_iSup]
  exact iSup_le hN

theorem step3Distance_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (D : ℕ) (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    mu ((interpolatedHighPair T) ⁻¹'
      pairStep3DistanceAt (0 : Site d) D) = 0 := by
  let c : ℝ≥0∞ := epsilon ^ (boxFinsetBK d D).card
  let p : ℝ≥0∞ := mu ((interpolatedHighPair T) ⁻¹'
    pairStep3DistanceAt (0 : Site d) D)
  by_contra hp
  have hc : c ≠ 0 := by
    exact pow_ne_zero _ hepsilon
  have hcp : c * p ≠ 0 := mul_ne_zero hc hp
  let L : ℝ≥0∞ := (((boxFinsetBK d D).card ^ 3 : ℕ) : ℝ≥0∞)
  obtain ⟨K, hK⟩ := ENNReal.exists_nat_mul_gt
    (a := c * p) (b := L) hcp (by simp [L])
  have hbound := step3Distance_probability_bound
    T mu D K epsilon hinsert
  have hrewrite : c * (K : ℝ≥0∞) * p = (K : ℝ≥0∞) * (c * p) := by
    ring
  rw [hrewrite] at hbound
  exact (not_lt_of_ge hbound) hK


theorem interpolatedHighPair_step3Core_measure_zero
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu] (epsilon : ℝ≥0∞)
    (hepsilon : epsilon ≠ 0)
    (hinsert : HasHighInsertionLowerBound mu T.threshold epsilon) :
    (interpolatedHighPairLaw T mu)
      (pairStep3CoreAt (0 : Site d)) = 0 := by
  have hpre : mu ((interpolatedHighPair T) ⁻¹'
      pairStep3CoreAt (0 : Site d)) = 0 := by
    rw [pairStep3CoreAt_eq_iUnion_distance,
      Set.preimage_iUnion]
    exact measure_iUnion_null fun D =>
      step3Distance_measure_zero T mu D epsilon hepsilon hinsert
  rw [interpolatedHighPairLaw,
    Measure.map_apply (measurable_interpolatedHighPair T)
      (measurableSet_pairStep3CoreAt 0)]
  exact hpre


theorem monotoneAutomaton_infiniteCluster_uniqueness
    (T : MonotoneAutomaton d) (mu : Measure (FieldTriple d))
    [IsProbabilityMeasure mu]
    (hd : 1 ≤ d) (herg : IsTripleFieldErgodic mu)
    (epsilon : ℝ≥0∞) (hepsilon : epsilon ≠ 0)
    (hinsertMiddle : HasMiddleInsertionLowerBound mu T.threshold epsilon)
    (hinsertHigh : HasHighInsertionLowerBound mu T.threshold epsilon)
    (hmono : ∀ᵐ q ∂mu, IsMonotoneFieldTriple q)
    (hlow : mu {q | 1 ≤ numInfiniteClusters d
      (siteToBond (T q.1))} = 1) :
    mu {q | numInfiniteClusters d (siteToBond (T q.2.2)) ≤ 1} = 1 := by
  apply highOutput_cluster_count_ae_le_one_of_step3Core
    T mu hd herg epsilon hepsilon hinsertMiddle hmono hlow
  exact interpolatedHighPair_step3Core_measure_zero
    T mu epsilon hepsilon hinsertHigh

end StatMech.FrontierA
