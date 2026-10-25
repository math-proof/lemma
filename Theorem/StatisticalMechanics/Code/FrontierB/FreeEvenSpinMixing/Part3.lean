/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FreeEvenSpinMixing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FreeParityErrorVanishing.Part2
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.FrontierB.FreeEvenSpinMixing.Part3
open Filter MeasureTheory Set Topology Function
open scoped BigOperators symmDiff


namespace StatMech.FrontierB

open ConfigSpace FK Ising Lattice Percolation Sharpness

variable {d : Nat}

theorem freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
    (hd : 1 ≤ d) {p : Real} (hp : 0 < p) (hp1 : p < 1)
    (B : Finset (Site d)) (k : Nat) :
    let mu := (freeInfiniteVolume d hp hp1
      (by norm_num : (0 : Real) < 2) :
        Measure (ConfigSpace (Sym2 (Site d))))
    mu.real (allClustersEvenEvent (hypercubicLattice d)
        (inverseAxisTranslateFinset hd k B)) =
      mu.real (allClustersEvenEvent (hypercubicLattice d) B) := by
  dsimp only
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  have hti : IsTranslationInvariant
      (G := Multiplicative (Site d)) mu :=
    bdp_freeIV_isTranslationInvariant hp hp1
  rw [show allClustersEvenEvent (hypercubicLattice d)
        (inverseAxisTranslateFinset hd k B) =
      shift (FK.freeAxisTranslationPower hd k) ⁻¹'
        allClustersEvenEvent (hypercubicLattice d) B by
      exact (preimage_allClustersEvenEvent_shift
        (FK.freeAxisTranslationPower hd k) B).symm]
  exact fmc_real_preimage_shift hti (FK.freeAxisTranslationPower hd k)
    (measurableSet_allClustersEvenEvent B)

theorem freeEvenParityFamilyTerm_nonneg
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card)
    (k : Nat) :
    let mu := (freeInfiniteVolume d
      (p := 1 - Real.exp (-2 * beta)) (q := 2)
      (by
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    0 ≤ freeEvenParityFamilyTerm hd mu A B k := by
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  by_cases hdisj : Disjoint A (inverseAxisTranslateFinset hd k B)
  · simp only [freeEvenParityFamilyTerm, if_pos hdisj, add_zero]
    have hgap := freeEvenParityMass_gap_nonneg_of_disjoint hd hbeta A
      (inverseAxisTranslateFinset hd k B) hAeven (by
        rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
          (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
        exact hBeven) hdisj
    have hgap' : 0 ≤
        mu.real (allClustersEvenEvent (hypercubicLattice d)
            (A ∪ inverseAxisTranslateFinset hd k B)) -
          mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
            mu.real (allClustersEvenEvent (hypercubicLattice d)
              (inverseAxisTranslateFinset hd k B)) := by
      simpa only [mu] using hgap
    rw [freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
      hd hp hp1 B k] at hgap'
    simpa only [freeEvenParityGap, mu] using hgap'
  · simp only [freeEvenParityFamilyTerm, if_neg hdisj]
    have hprod : mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) ≤ 1 :=
      mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
    have hmass : 0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) := measureReal_nonneg
    dsimp [freeEvenParityGap, mu]
    linarith

theorem freeEvenParityFamilyTerm_average_tendsto_zero
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (A B : Finset (Site d)) (hAeven : Even A.card) (hBeven : Even B.card) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    Tendsto (fun n : Nat => (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      freeEvenParityFamilyTerm hd mu A B k) atTop (nhds 0) := by
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  have hgap := freeEvenParityGap_average_tendsto_zero
    hd hp hp1 A B hAeven hBeven
  obtain ⟨R, hAR⟩ := Lattice.finite_subset_box
    (A : Set (Site d)) A.finite_toSet
  have hdisj : ∀ᶠ k in atTop,
      Disjoint A (inverseAxisTranslateFinset hd k B) := by
    filter_upwards [inverseAxisTranslateFinset_eventually_outside_box hd B R]
      with k hk
    rw [Finset.disjoint_left]
    intro x hxA hxB
    exact hk hxB (hAR hxA)
  let penalty : Nat → Real := fun k =>
    if Disjoint A (inverseAxisTranslateFinset hd k B) then 0 else 2
  have hpenalty : Tendsto penalty atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hdisj] with k hk
    simp [penalty, hk]
  have hpenaltyAvg := hpenalty.cesaro
  have hadd := hgap.add hpenaltyAvg
  simpa only [zero_add, freeEvenParityFamilyTerm, penalty,
    Finset.sum_add_distrib, mul_add, mu, p] using hadd


theorem freeInfiniteVolume_evenParity_family_pairMixing_after
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (K : Nat)
    (supports : Finset (Finset (Site d)))
    (heven : ∀ A ∈ supports, Even A.card)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    ∃ k : Nat, K ≤ k ∧
      ∀ A ∈ supports, ∀ B ∈ supports,
        Disjoint A (B.image fun x =>
          (FK.freeAxisTranslationPower hd k)⁻¹ • x) ∧
        abs (mu.real (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x =>
                (FK.freeAxisTranslationPower hd k)⁻¹ • x)) -
            mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
              mu.real (allClustersEvenEvent (hypercubicLattice d) B)) <
          epsilon := by
  classical
  dsimp only
  let p := 1 - Real.exp (-2 * beta)
  have hp : 0 < p := by
    dsimp [p]
    apply sub_pos.mpr
    rw [Real.exp_lt_one_iff]
    linarith
  have hp1 : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-2 * beta)]
  let mu := (freeInfiniteVolume d hp hp1
    (by norm_num : (0 : Real) < 2) :
      Measure (ConfigSpace (Sym2 (Site d))))
  let delta := min epsilon (1 / 2 : Real)
  have hdelta : 0 < delta := lt_min hepsilon (by norm_num)
  have hbase : Tendsto (fun n : Nat =>
      ∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k)
      atTop (nhds 0) := by
    convert tendsto_finsetSum supports (fun A hA =>
      tendsto_finsetSum supports (fun B hB =>
        freeEvenParityFamilyTerm_average_tendsto_zero hd hbeta A B
          (heven A hA) (heven B hB))) using 1 <;>
      simp only [Finset.sum_const_zero]
  let latePenalty : Nat → Real := fun k => if K ≤ k then 0 else 2
  have hlate : Tendsto latePenalty atTop (nhds 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop K] with k hk
    simp [latePenalty, hk]
  have htotal : Tendsto (fun n : Nat =>
      (∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k) +
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k)
      atTop (nhds 0) := by
    simpa only [zero_add] using hbase.add hlate.cesaro
  have hevent : ∀ᶠ n : Nat in atTop,
      ((∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
        ∑ k ∈ Finset.range n, freeEvenParityFamilyTerm hd mu A B k) +
        (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k) <
        delta := htotal.eventually (eventually_lt_nhds hdelta)
  obtain ⟨n, hn, havg⟩ := ((eventually_ge_atTop 1).and hevent).exists
  have havg' : (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
      ((∑ A ∈ supports, ∑ B ∈ supports,
        freeEvenParityFamilyTerm hd mu A B k) + latePenalty k) < delta := by
    calc
      (n : Real)⁻¹ * ∑ k ∈ Finset.range n,
          ((∑ A ∈ supports, ∑ B ∈ supports,
            freeEvenParityFamilyTerm hd mu A B k) + latePenalty k) =
          (∑ A ∈ supports, ∑ B ∈ supports, (n : Real)⁻¹ *
            ∑ k ∈ Finset.range n,
              freeEvenParityFamilyTerm hd mu A B k) +
            (n : Real)⁻¹ * ∑ k ∈ Finset.range n, latePenalty k := by
        rw [Finset.sum_add_distrib, mul_add]
        congr 1
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro A hA
        rw [Finset.sum_comm]
      _ < delta := havg
  have hnR : (0 : Real) < n := by positivity
  have hsumlt :
      (∑ k ∈ Finset.range n,
        ((∑ A ∈ supports, ∑ B ∈ supports,
          freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) <
      ∑ _k ∈ Finset.range n, delta := by
    calc
      (∑ k ∈ Finset.range n,
          ((∑ A ∈ supports, ∑ B ∈ supports,
            freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) =
          (n : Real) * ((n : Real)⁻¹ * ∑ k ∈ Finset.range n,
            ((∑ A ∈ supports, ∑ B ∈ supports,
              freeEvenParityFamilyTerm hd mu A B k) + latePenalty k)) := by
        field_simp
      _ < (n : Real) * delta := mul_lt_mul_of_pos_left havg' hnR
      _ = ∑ _k ∈ Finset.range n, delta := by simp
  obtain ⟨k, hk, hkdelta⟩ := Finset.exists_lt_of_sum_lt hsumlt
  have hsumNonneg : 0 ≤ ∑ A ∈ supports, ∑ B ∈ supports,
      freeEvenParityFamilyTerm hd mu A B k :=
    Finset.sum_nonneg fun A hA => Finset.sum_nonneg fun B hB =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A B
        (heven A hA) (heven B hB) k
  have hkK : K ≤ k := by
    by_contra hnot
    have hpen : latePenalty k = 2 := by simp [latePenalty, hnot]
    have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
    rw [hpen] at hkdelta
    linarith
  refine ⟨k, hkK, ?_⟩
  intro A hA B hB
  have hinner : freeEvenParityFamilyTerm hd mu A B k ≤
      ∑ B' ∈ supports, freeEvenParityFamilyTerm hd mu A B' k :=
    Finset.single_le_sum (fun B' hB' =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A B'
        (heven A hA) (heven B' hB') k) hB
  have houter : (∑ B' ∈ supports,
      freeEvenParityFamilyTerm hd mu A B' k) ≤
      ∑ A' ∈ supports, ∑ B' ∈ supports,
        freeEvenParityFamilyTerm hd mu A' B' k :=
    Finset.single_le_sum (fun A' hA' => Finset.sum_nonneg fun B' hB' =>
      freeEvenParityFamilyTerm_nonneg hd hbeta A' B'
        (heven A' hA') (heven B' hB') k) hA
  have hterm : freeEvenParityFamilyTerm hd mu A B k < delta :=
    lt_of_le_of_lt (hinner.trans (houter.trans (by
      have hlateNonneg : 0 ≤ latePenalty k := by
        dsimp [latePenalty]
        split <;> norm_num
      linarith))) hkdelta
  have hdisj : Disjoint A (inverseAxisTranslateFinset hd k B) := by
    by_contra hnot
    have hprod : mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
        mu.real (allClustersEvenEvent (hypercubicLattice d) B) ≤ 1 :=
      mul_le_one₀ measureReal_le_one measureReal_nonneg measureReal_le_one
    have hmass : 0 ≤ mu.real (allClustersEvenEvent (hypercubicLattice d)
        (A ∪ inverseAxisTranslateFinset hd k B)) := measureReal_nonneg
    have hdeltaHalf : delta ≤ 1 / 2 := min_le_right _ _
    dsimp [freeEvenParityFamilyTerm, freeEvenParityGap] at hterm
    rw [if_neg hnot] at hterm
    linarith
  refine ⟨hdisj, ?_⟩
  have hgapNonneg := freeEvenParityMass_gap_nonneg_of_disjoint hd hbeta A
    (inverseAxisTranslateFinset hd k B) (heven A hA) (by
      rw [inverseAxisTranslateFinset, Finset.card_image_of_injective _
        (MulAction.injective (FK.freeAxisTranslationPower hd k)⁻¹)]
      exact heven B hB) hdisj
  have hgapNonneg' : 0 ≤
      mu.real (allClustersEvenEvent (hypercubicLattice d)
          (A ∪ inverseAxisTranslateFinset hd k B)) -
        mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
          mu.real (allClustersEvenEvent (hypercubicLattice d)
            (inverseAxisTranslateFinset hd k B)) := by
    simpa only [mu] using hgapNonneg
  rw [freeInfiniteVolume_allClustersEven_inverseTranslate_real_eq
    hd hp hp1 B k] at hgapNonneg'
  have hgaplt : freeEvenParityGap hd mu A B k < epsilon := by
    have hdeltaEps : delta ≤ epsilon := min_le_left _ _
    dsimp [freeEvenParityFamilyTerm] at hterm
    rw [if_pos hdisj, add_zero] at hterm
    exact hterm.trans_le hdeltaEps
  change abs (freeEvenParityGap hd mu A B k) < epsilon
  rw [abs_of_nonneg (by
    simpa only [freeEvenParityGap, mu] using hgapNonneg')]
  exact hgaplt

theorem freeInfiniteVolume_evenParity_family_pairMixing
    (hd : 1 ≤ d) {beta : Real} (hbeta : 0 < beta)
    (supports : Finset (Finset (Site d)))
    (heven : ∀ A ∈ supports, Even A.card)
    (epsilon : Real) (hepsilon : 0 < epsilon) :
    let p := 1 - Real.exp (-2 * beta)
    let mu := (freeInfiniteVolume d
      (p := p) (q := 2)
      (by
        dsimp [p]
        apply sub_pos.mpr
        rw [Real.exp_lt_one_iff]
        linarith)
      (by
        dsimp [p]
        linarith [Real.exp_pos (-2 * beta)])
      (by norm_num : (0 : Real) < 2) : Measure _)
    ∃ g : Multiplicative (Site d),
      ∀ A ∈ supports, ∀ B ∈ supports,
        Disjoint A (B.image fun x => g⁻¹ • x) ∧
        abs (mu.real (allClustersEvenEvent (hypercubicLattice d)
              (A ∪ B.image fun x => g⁻¹ • x)) -
            mu.real (allClustersEvenEvent (hypercubicLattice d) A) *
              mu.real (allClustersEvenEvent (hypercubicLattice d) B)) <
          epsilon := by
  obtain ⟨k, hk, hmix⟩ := freeInfiniteVolume_evenParity_family_pairMixing_after
    hd hbeta 0 supports heven epsilon hepsilon
  exact ⟨FK.freeAxisTranslationPower hd k, hmix⟩

end StatMech.FrontierB
