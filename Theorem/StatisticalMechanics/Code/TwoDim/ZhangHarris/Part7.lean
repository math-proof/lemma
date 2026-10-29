/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InfiniteHarris.Part3
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangFixedK.Part12
import Theorem.StatisticalMechanics.Code.Percolation.DctItem2.Part2
import Def.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal


namespace StatMech.TwoDim

open StatMech.Lattice StatMech.Percolation StatMech.Universality

open StatMech.RSW.Box

theorem zih_sideFamily_dependsOn {A : Set (ConfigSpace (Sym2 (Site 2)))}
    {F : Finset (Sym2 (Site 2))} (hA : StatMech.DependsOn A F) (i : Fin 4) :
    StatMech.DependsOn (zrs_sideFamily A i) (zih_sideSupport F i) := by
  fin_cases i
  · exact hA
  · exact zih_rot_dependsOn (zih_rot_dependsOn hA)
  · exact zih_rot_dependsOn hA
  · exact zih_rot_dependsOn (zih_rot_dependsOn (zih_rot_dependsOn hA))

theorem zih_complUnion_bound_of_finite_dependsOn
    {A B : Set (ConfigSpace (Sym2 (Site 2)))} (F : Finset (Sym2 (Site 2)))
    (hAdep : StatMech.DependsOn A F) (hBdep : StatMech.DependsOn B F)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B) :
    (1 - halfMeasure.real A) * (1 - halfMeasure.real B) ≤
      1 - halfMeasure.real (A ∪ B) := by
  have hfkg := ih_harris_of_finite_dependsOn half_le_one F
    hAdep hBdep hAinc hBinc
  change halfMeasure.real A * halfMeasure.real B ≤ halfMeasure.real (A ∩ B) at hfkg
  have hie : halfMeasure.real (A ∪ B) + halfMeasure.real (A ∩ B) =
      halfMeasure.real A + halfMeasure.real B :=
    measureReal_union_add_inter hBm
  nlinarith

theorem zih_complUnion_four_of_finite_dependsOn
    {A B C D : Set (ConfigSpace (Sym2 (Site 2)))} (F : Finset (Sym2 (Site 2)))
    (hAdep : StatMech.DependsOn A F) (hBdep : StatMech.DependsOn B F)
    (hCdep : StatMech.DependsOn C F) (hDdep : StatMech.DependsOn D F)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (hCinc : IsIncreasing C) (hDinc : IsIncreasing D)
    (hAm : MeasurableSet A) (hBm : MeasurableSet B)
    (hCm : MeasurableSet C) (hDm : MeasurableSet D) :
    (1 - halfMeasure.real A) * (1 - halfMeasure.real B) *
        (1 - halfMeasure.real C) * (1 - halfMeasure.real D) ≤
      1 - halfMeasure.real (A ∪ B ∪ C ∪ D) := by
  have hABdep : StatMech.DependsOn (A ∪ B) F := by
    intro omega omega' hagree
    simp only [Set.mem_union, hAdep omega omega' hagree, hBdep omega omega' hagree]
  have hABCdep : StatMech.DependsOn (A ∪ B ∪ C) F := by
    intro omega omega' hagree
    simp only [Set.mem_union, hAdep omega omega' hagree, hBdep omega omega' hagree,
      hCdep omega omega' hagree]
  have h1 := zih_complUnion_bound_of_finite_dependsOn F hAdep hBdep
    hAinc hBinc hAm hBm
  have h2 := zih_complUnion_bound_of_finite_dependsOn F hABdep hCdep
    (hAinc.union hBinc) hCinc (hAm.union hBm) hCm
  have h3 := zih_complUnion_bound_of_finite_dependsOn F hABCdep hDdep
    ((hAinc.union hBinc).union hCinc) hDinc ((hAm.union hBm).union hCm) hDm
  have nC : 0 ≤ 1 - halfMeasure.real C := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := C)]
  have nD : 0 ≤ 1 - halfMeasure.real D := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := D)]
  calc
    _ ≤ (1 - halfMeasure.real (A ∪ B)) * (1 - halfMeasure.real C) *
        (1 - halfMeasure.real D) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 nC) nD
    _ ≤ (1 - halfMeasure.real (A ∪ B ∪ C)) *
        (1 - halfMeasure.real D) := mul_le_mul_of_nonneg_right h2 nD
    _ ≤ _ := h3

theorem zih_sideApprox_antitone (k N : ℕ) (i : Fin 4) :
    Antitone (fun m => zrs_sideFamily (zih_LeftArmApprox k N m) i) := by
  intro m n hmn
  have hbase := zih_LeftArmApprox_antitone k N hmn
  fin_cases i
  · exact hbase
  · exact Set.preimage_mono (Set.preimage_mono hbase)
  · exact Set.preimage_mono hbase
  · exact Set.preimage_mono (Set.preimage_mono (Set.preimage_mono hbase))

theorem zih_sideApprox_iInter (k N : ℕ) (i : Fin 4) :
    (⋂ m, zrs_sideFamily (zih_LeftArmApprox k N m) i) =
      zrs_sideFamily (zfk_LeftArmEvent k N) i := by
  rw [zih_LeftArmEvent_eq_iInter]
  fin_cases i <;> ext omega <;>
    simp [zrs_sideFamily, zrs_rot]

theorem zih_complUnion_four_left (k N : ℕ) :
    let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
    (1 - halfMeasure.real (S 0)) * (1 - halfMeasure.real (S 1)) *
        (1 - halfMeasure.real (S 2)) * (1 - halfMeasure.real (S 3)) ≤
      1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
  let S : Fin 4 → ℕ → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i m => zrs_sideFamily (zih_LeftArmApprox k N m) i
  let F : ℕ → Finset (Sym2 (Site 2)) := fun m =>
    Finset.univ.biUnion (fun i : Fin 4 => zih_sideSupport (zih_leftApproxSupport k N m) i)
  have hdep : ∀ i m, StatMech.DependsOn (S i m) (F m) := by
    intro i m
    apply (zih_sideFamily_dependsOn (zih_LeftArmApprox_dependsOn k N m) i).mono
    intro e he
    change e ∈ Finset.univ.biUnion
      (fun i : Fin 4 => zih_sideSupport (zih_leftApproxSupport k N m) i)
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, he⟩
  have hinc : ∀ i m, IsIncreasing (S i m) := fun i m =>
    zrs_sideFamily_isIncreasing (zih_LeftArmApprox_isIncreasing k N m) i
  have hmeas : ∀ i m, MeasurableSet (S i m) := fun i m =>
    zrs_sideFamily_measurableSet (zih_LeftArmApprox_measurableSet k N m) i
  have hstage : ∀ m,
      (1 - halfMeasure.real (S 0 m)) * (1 - halfMeasure.real (S 1 m)) *
          (1 - halfMeasure.real (S 2 m)) * (1 - halfMeasure.real (S 3 m)) ≤
        1 - halfMeasure.real (S 0 m ∪ S 1 m ∪ S 2 m ∪ S 3 m) := by
    intro m
    exact zih_complUnion_four_of_finite_dependsOn (F m)
      (hdep 0 m) (hdep 1 m) (hdep 2 m) (hdep 3 m)
      (hinc 0 m) (hinc 1 m) (hinc 2 m) (hinc 3 m)
      (hmeas 0 m) (hmeas 1 m) (hmeas 2 m) (hmeas 3 m)
  let U : ℕ → Set (ConfigSpace (Sym2 (Site 2))) := fun m => ⋃ i : Fin 4, S i m
  have hUeq (m : ℕ) : U m = S 0 m ∪ S 1 m ∪ S 2 m ∪ S 3 m := by
    ext omega
    simp only [U, Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro h
      rcases h with ((h0 | h1) | h2) | h3
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
  have hUanti : Antitone U := by
    intro m n hmn omega
    simp only [U, Set.mem_iUnion]
    rintro ⟨i, hi⟩
    exact ⟨i, zih_sideApprox_antitone k N i hmn hi⟩
  have hUmeas : ∀ m, MeasurableSet (U m) := fun m => by
    apply MeasurableSet.iUnion
    exact fun i => hmeas i m
  have hSi : ∀ i, (⋂ m, S i m) = zrs_sideFamily (zfk_LeftArmEvent k N) i :=
    fun i => zih_sideApprox_iInter k N i
  have hUi : (⋂ m, U m) = ⋃ i : Fin 4, zrs_sideFamily (zfk_LeftArmEvent k N) i := by
    change (⋂ m, ⋃ i : Fin 4, S i m) = _
    rw [iInter_iUnion_of_antitone (fun i => zih_sideApprox_antitone k N i)]
    congr 1
    funext i
    exact hSi i
  have hT (i : Fin 4) : Tendsto (fun m => halfMeasure.real (S i m)) atTop
      (nhds (halfMeasure.real (zrs_sideFamily (zfk_LeftArmEvent k N) i))) := by
    rw [← hSi i]
    exact ih_tendsto_measureReal_iInter halfMeasure (S i)
      (zih_sideApprox_antitone k N i) (hmeas i)
  have hUT : Tendsto (fun m => halfMeasure.real (U m)) atTop
      (nhds (halfMeasure.real (⋃ i : Fin 4, zrs_sideFamily (zfk_LeftArmEvent k N) i))) := by
    rw [← hUi]
    exact ih_tendsto_measureReal_iInter halfMeasure U hUanti hUmeas
  have hleft := (((hT 0).const_sub 1).mul ((hT 1).const_sub 1)).mul
    ((hT 2).const_sub 1) |>.mul ((hT 3).const_sub 1)
  have hright := hUT.const_sub 1
  have hlim := le_of_tendsto_of_tendsto hleft hright
    (Filter.Eventually.of_forall fun m => by simpa [hUeq m] using hstage m)
  let T := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
  change (1 - halfMeasure.real (T 0)) * (1 - halfMeasure.real (T 1)) *
      (1 - halfMeasure.real (T 2)) * (1 - halfMeasure.real (T 3)) ≤
    1 - halfMeasure.real (T 0 ∪ T 1 ∪ T 2 ∪ T 3)
  have hTU : (⋃ i : Fin 4, T i) = T 0 ∪ T 1 ∪ T 2 ∪ T 3 := by
    ext omega
    simp only [Set.mem_iUnion, Set.mem_union]
    constructor
    · rintro ⟨i, hi⟩
      fin_cases i <;> simp_all
    · intro h
      rcases h with ((h0 | h1) | h2) | h3
      · exact ⟨0, h0⟩
      · exact ⟨1, h1⟩
      · exact ⟨2, h2⟩
      · exact ⟨3, h3⟩
  rwa [hTU] at hlim

theorem zih_sqrt_trick_left (k N : ℕ) :
    let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
    1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
        ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by
  let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i
  have hprod := zih_complUnion_four_left k N
  have hsym (i : Fin 4) : halfMeasure.real (S i) = halfMeasure.real (S 0) :=
    zrs_side_symmetry (zfk_LeftArmEvent_measurableSet k N) i
  have hpow : (1 - halfMeasure.real (S 0)) ^ 4 ≤
      1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    have hrw : (1 - halfMeasure.real (S 0)) * (1 - halfMeasure.real (S 1)) *
        (1 - halfMeasure.real (S 2)) * (1 - halfMeasure.real (S 3)) =
        (1 - halfMeasure.real (S 0)) ^ 4 := by
      rw [hsym 1, hsym 2, hsym 3]
      ring
    linarith
  have nA : 0 ≤ 1 - halfMeasure.real (S 0) := by
    linarith [measureReal_le_one (μ := halfMeasure) (s := S 0)]
  set u := halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)
  have hroot : 1 - halfMeasure.real (S 0) ≤ (1 - u) ^ ((1 : ℝ) / 4) := by
    have hmono : ((1 - halfMeasure.real (S 0)) ^ 4) ^ ((1 : ℝ) / 4) ≤
        (1 - u) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hpow (by norm_num)
    have hreduce : ((1 - halfMeasure.real (S 0)) ^ 4 : ℝ) ^ ((1 : ℝ) / 4) =
        1 - halfMeasure.real (S 0) := by
      rw [← Real.rpow_natCast (1 - halfMeasure.real (S 0)) 4,
        ← Real.rpow_mul nA]
      norm_num
    rwa [hreduce] at hmono
  linarith

theorem zih_armLower_le_left (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
  let S : Fin 4 → Set (ConfigSpace (Sym2 (Site 2))) :=
    fun i => zrs_sideFamily (zfk_LeftArmEvent k N) i
  have hsqrt := zih_sqrt_trick_left k N
  have hmono : halfMeasure.real (zbd_boxHitsInfinite k) ≤
      halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) :=
    measureReal_mono (zfk_boxHitsInfinite_subset_armUnion k N hkN)
      (measure_ne_top _ _)
  have hU0 : 0 ≤ 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
    linarith [measureReal_le_one (μ := halfMeasure)
      (s := S 0 ∪ S 1 ∪ S 2 ∪ S 3)]
  have hcomp : 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) ≤
      1 - halfMeasure.real (zbd_boxHitsInfinite k) := by linarith
  have hrpow := Real.rpow_le_rpow hU0 hcomp (by norm_num : (0 : ℝ) ≤ 1 / 4)
  change 1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) at hsqrt
  change (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^
      ((1 : ℝ) / 4) ≤
    (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^ ((1 : ℝ) / 4) at hrpow
  have hfinal : 1 - (1 - halfMeasure.real (zbd_boxHitsInfinite k)) ^
      ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by linarith
  simpa [zfk_armLower, S] using hfinal

theorem zih_armLower_le_right (k N : ℕ) (hkN : k ≤ N) :
    zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
  rw [zfk_right_prob_eq_left]
  exact zih_armLower_le_left k N hkN

theorem zih_fixedK_contradiction
    (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2))
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    False := by
  have hk : ∀ k, zfk_armLower k * zfk_armLower k ≤ (1 : ℝ) / 2 := by
    intro k
    have hpoint : ∀ N, k + 1 ≤ N →
        zfk_armLower k * zfk_armLower k ≤ (1 : ℝ) / 2 +
          halfMeasure.real (zfk_pairErrorUnion k N) := by
      intro N hkN
      calc
        zfk_armLower k * zfk_armLower k ≤
            halfMeasure.real (zfk_LeftArmEvent k N) *
              halfMeasure.real (zfk_RightArmEvent k N) := by
          exact mul_le_mul (zih_armLower_le_left k N (by omega))
            (zih_armLower_le_right k N (by omega))
            (zfk_armLower_nonneg k) measureReal_nonneg
        _ ≤ halfMeasure.real (zfk_ArmPairEvent k N) := zih_armPair_fkg k N
        _ ≤ halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
              (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) +
              halfMeasure.real (zfk_pairErrorUnion k N) :=
          zfk_armPair_probability_le_crossing_add_error k N
        _ ≤ (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N) := by
          gcongr
          exact hhalf N
    have hlim : Tendsto
        (fun N => (1 : ℝ) / 2 + halfMeasure.real (zfk_pairErrorUnion k N))
        atTop (nhds ((1 : ℝ) / 2)) := by
      simpa using tendsto_const_nhds.add (zfk_pairErrorUnion_tendsto_zero k)
    exact le_of_tendsto_of_tendsto tendsto_const_nhds hlim
      ((eventually_ge_atTop (k + 1)).mono fun N hN => hpoint N hN)
  have hq := zfk_armLower_tendsto_one hpos
  have hqq : Tendsto (fun k => zfk_armLower k * zfk_armLower k)
      atTop (nhds 1) := by
    simpa using hq.mul hq
  have hbad : (1 : ℝ) ≤ (1 : ℝ) / 2 :=
    le_of_tendsto_of_tendsto hqq tendsto_const_nhds
      (Filter.Eventually.of_forall hk)
  norm_num at hbad

theorem zih_thetaReal_zero_of_matched_half
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    halfMeasure.real (Universality.percolationEvent 2) = 0 := by
  by_contra hne
  exact zih_fixedK_contradiction
    (lt_of_le_of_ne measureReal_nonneg (Ne.symm hne)) hhalf

theorem zih_percolationProbability_zero_of_matched_half
    (hhalf : ∀ N : ℕ,
      halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent
        (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
    Universality.percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 := by
  unfold Universality.percolationProbability
  have hr := zih_thetaReal_zero_of_matched_half hhalf
  have hle : halfMeasure (Universality.percolationEvent 2) ≤ 1 :=
    le_trans (measure_mono (subset_univ _)) (by simp [measure_univ])
  exact (ENNReal.toReal_eq_zero_iff _).mp hr |>.resolve_right
    (ne_top_of_le_ne_top (by simp) hle)

theorem zih_percolationProbability_zero_of_faithful_exclusive
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
    Universality.percolationProbability 2 (2⁻¹ : NNReal) half_le_one = 0 :=
  zih_percolationProbability_zero_of_matched_half
    (fun N => zfk_matched_half_of_faithful_exclusive N (hexcl N))

theorem zih_criticalProbability_eq_half_of_faithful_exclusive
    (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
    (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
    (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
    (hmeasThin : ∀ n : ℤ, 0 < n →
      MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
    criticalProbability 2 = (1 : ℝ) / 2 := by
  have hge : (1 : ℝ) / 2 ≤ criticalProbability 2 :=
    half_le_criticalProbability_of_subcritical
      (zih_percolationProbability_zero_of_faithful_exclusive hexcl)
  have hle := kbw_criticalProbability_le_half_square_faithful
    hmeasGenH hmeasFace hmeasThin
  linarith


end StatMech.TwoDim
