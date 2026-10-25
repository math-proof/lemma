/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part2
open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem freeEvenParityGap_average_tendsto_zero
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) : Measure (ConfigSpace (Sym2 (Site d))))
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      freeEvenParityGap hd mu A B k) atTop (nhds 0) := by
  dsimp only
  let phi := freeInfiniteVolume d hp hp1 (by norm_num : (0 : Real) < 2)
  let mu := (phi : Measure (ConfigSpace (Sym2 (Site d))))
  let EA := allClustersEvenEvent (hypercubicLattice d) A
  let EB := allClustersEvenEvent (hypercubicLattice d) B
  have hcorr := freeInfiniteVolume_eventPairCorrelationAverage_tendsto
    hd hp hp1 EA EB (measurableSet_allClustersEvenEvent A)
      (measurableSet_allClustersEvenEvent B)
  have hinter : Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      (mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) -
        mu.real EA * mu.real EB)) atTop (nhds 0) := by
    have hcorr' : Tendsto (fun n : Nat => (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n,
          mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB))
        atTop (nhds (mu.real EA * mu.real EB)) := by
      simpa only [mu, phi] using hcorr
    have hc : Tendsto (fun _ : Nat => mu.real EA * mu.real EB) atTop
        (nhds (mu.real EA * mu.real EB)) := tendsto_const_nhds
    have hsub := hcorr'.sub hc
    simp only [sub_self] at hsub
    apply hsub.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]
    have hnR : (n : Real) ≠ 0 := Nat.cast_ne_zero.mpr hn
    field_simp
  obtain ⟨R, hAR⟩ := Lattice.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  have hdisj : ∀ᶠ k in atTop,
      Disjoint A (inverseAxisTranslateFinset hd k B) := by
    filter_upwards [inverseAxisTranslateFinset_eventually_outside_box hd B R]
      with k hk
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hk hxB (hAR hxA)
  have hunique : mu (atLeastTwoInfinite d) = 0 := by
    exact (freeInfinite_q2_canonical_uniqueness_all_parameters hd hp hp1).2.1
  have herr := twoOddCrossClusters_axisTranslate_real_tendsto_zero
    hd phi hunique A B
  let D : Nat → Real := fun k =>
    mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) -
      mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB)
  have hD : Tendsto D atTop (nhds 0) := by
    apply squeeze_zero' (g := fun k => mu.real
      (twoOddCrossClustersEvent (hypercubicLattice d) A
        (inverseAxisTranslateFinset hd k B)))
    · filter_upwards [hdisj] with k hk
      have hpre : shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB =
          allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B) := by
        exact preimage_allClustersEvenEvent_shift
          (FK.freeAxisTranslationPower hd k) B
      have hsub : EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB ⊆
          allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) := by
        rw [hpre]
        intro omega homega
        exact allClustersEven_union_of_disjoint (hypercubicLattice d) omega A
          (inverseAxisTranslateFinset hd k B) hk homega.1 homega.2
      exact sub_nonneg.mpr (measureReal_mono hsub)
    · filter_upwards [hdisj] with k hk
      have hpre : shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB =
          allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B) :=
        preimage_allClustersEvenEvent_shift (FK.freeAxisTranslationPower hd k) B
      have hsub : EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB ⊆
          allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) := by
        rw [hpre]
        intro omega homega
        exact allClustersEven_union_of_disjoint (hypercubicLattice d) omega A
          (inverseAxisTranslateFinset hd k B) hk homega.1 homega.2
      have hdiff := allClustersEven_factorization_error_subset
        (hypercubicLattice d) A (inverseAxisTranslateFinset hd k B) hk hAeven
          (by
            rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
              (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
            exact hBeven)
      have hdiff' : allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) \
            (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) ⊆
          twoOddCrossClustersEvent (hypercubicLattice d) A
            (inverseAxisTranslateFinset hd k B) := by
        rwa [hpre]
      have heq : D k = mu.real
          (allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B) \
            (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB)) := by
        dsimp [D]
        rw [measureReal_diff hsub
          ((measurableSet_allClustersEvenEvent A).inter
            ((measurableSet_allClustersEvenEvent B).preimage
              (measurable_shift (FK.freeAxisTranslationPower hd k))))]
      rw [heq]
      have hfinite : mu
          (twoOddCrossClustersEvent (hypercubicLattice d) A
            (inverseAxisTranslateFinset hd k B)) ≠ ⊤ := measure_ne_top mu _
      exact measureReal_mono hdiff' (by exact hfinite)
    · exact herr
  have hDavg := hD.cesaro
  have hsum : Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
        (mu.real (EA ∩ shift (FK.freeAxisTranslationPower hd k) ⁻¹' EB) -
          mu.real EA * mu.real EB) +
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n, D k) atTop (nhds 0) := by
    simpa only [zero_add] using hinter.add hDavg
  apply hsum.congr'
  filter_upwards with n
  dsimp [D, freeEvenParityGap, EA, EB, mu]
  rw [← mul_add, ← Finset.sum_add_distrib]
  apply congrArg (fun z : Real => (n : Real)⁻¹ * z)
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem freeState_spinProd_gks_second
    (d : Nat) (beta : Real) (hbeta : 0 ≤ beta)
    (A B : Finset (Site d)) :
    (∫ sigma, spinProd A sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) *
      (∫ sigma, spinProd B sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d)))) ≤
      ∫ sigma, spinProd (A ∆ B) sigma
        ∂(freeState d beta 0 : Measure (ConfigSpace (Site d))) := by
  have hAconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta A
  have hBconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta B
  have hABconv := integral_freeMeasure_spinProd_tendsto_freeState
    d beta hbeta (A ∆ B)
  apply le_of_tendsto_of_tendsto (hAconv.mul hBconv) hABconv
  obtain ⟨R, hR⟩ := Lattice.finite_subset_box
    ((A : Set (Site d)) ∪ (B : Set (Site d)))
    (A.finite_toSet.union B.finite_toSet)
  filter_upwards [eventually_ge_atTop R] with n hn
  have hAn : (A : Set (Site d)) ⊆ box d n :=
    (fun x hx => box_mono d hn (hR (Or.inl hx)))
  have hBn : (B : Set (Site d)) ⊆ box d n :=
    (fun x hx => box_mono d hn (hR (Or.inr hx)))
  have hABn : ((A ∆ B : Finset (Site d)) : Set (Site d)) ⊆ box d n := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_symmDiff] at hx
    exact hx.elim (fun h => hAn h.1) (fun h => hBn h.1)
  rw [integral_freeMeasure_spinProd d n beta 0 A hAn,
    integral_freeMeasure_spinProd d n beta 0 B hBn,
    integral_freeMeasure_spinProd d n beta 0 (A ∆ B) hABn]
  have hsupport : boxSpinSupport d n (A ∆ B) =
      boxSpinSupport d n A ∆ boxSpinSupport d n B := by
    ext x
    simp only [boxSpinSupport, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_symmDiff]
  rw [hsupport]
  exact gks_second (sctBoxGraph d n) beta 0 hbeta le_rfl
    (boxSpinSupport d n A) (boxSpinSupport d n B)

theorem freeEvenParityMass_gap_nonneg_of_disjoint
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card)
    (hdisj : Disjoint A B) :
    let mu := (freeInfiniteVolume d
      (p := 1 - Real.exp (-2 * beta)) (q := 2)
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d) (A ∪ B)) -
      mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) := by
  dsimp only
  have hUnionEven : Even (A ∪ B).card := by
    rw [Finset.card_union_of_disjoint hdisj]
    exact hAeven.add hBeven
  have hsymm : A ∆ B = A ∪ B := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_union]
    constructor
    · intro h
      rcases h with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · intro h
      rcases h with hx | hx
      · left
        exact ⟨hx, fun hy => Finset.disjoint_left.1 hdisj hx hy⟩
      · right
        exact ⟨hx, fun hy => Finset.disjoint_left.1 hdisj hy hx⟩
  rw [← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd (A ∪ B) hUnionEven,
    ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd A hAeven,
    ← integral_freeState_spinProd_eq_freeInfinite_allClustersEven
      d beta hbeta hd B hBeven,
    sub_nonneg, ← hsymm]
  exact freeState_spinProd_gks_second d beta hbeta.le A B

end StatMech.FrontierB
