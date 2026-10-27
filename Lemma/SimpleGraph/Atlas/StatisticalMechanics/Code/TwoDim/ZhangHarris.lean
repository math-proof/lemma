import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.TwoDim.ZhangHarris.Part7
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[zih_clusterApprox_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_clusterApprox_dependsOn_eq
  {x : Site 2}
  {m : ℕ} :
-- imply
  StatMech.DependsOn (zih_clusterApprox x m) (zih_clusterSupport x m) := by
-- proof
  apply StatMech.TwoDim.zih_clusterApprox_dependsOn x m

/--
[zih_clusterApprox_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_clusterApprox_isIncreasing_eq
  {x : Site 2}
  {m : ℕ} :
-- imply
  IsIncreasing (zih_clusterApprox x m) := by
-- proof
  apply StatMech.TwoDim.zih_clusterApprox_isIncreasing x m

/--
[zih_clusterApprox_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_clusterApprox_measurableSet_eq
  {x : Site 2}
  {m : ℕ} :
-- imply
  MeasurableSet (zih_clusterApprox x m) := by
-- proof
  apply StatMech.TwoDim.zih_clusterApprox_measurableSet x m

/--
[zih_clusterApprox_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_clusterApprox_antitone_eq
  {x : Site 2} :
-- imply
  Antitone (zih_clusterApprox x) := by
-- proof
  apply StatMech.TwoDim.zih_clusterApprox_antitone x

/--
[zih_cluster_shift_infinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_cluster_shift_infinite_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2} :
-- imply
  (cluster 2 (ConfigSpace.shift (zih_centerShift x) omega) (origin 2)).Infinite ↔ (cluster 2 omega x).Infinite := by
-- proof
  apply StatMech.TwoDim.zih_cluster_shift_infinite_iff omega x

/--
[zih_clusterInfinite_eq_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_clusterInfinite_eq_iInter_eq
  {x : Site 2} :
-- imply
  {omega : ConfigSpace (Sym2 (Site 2)) | (cluster 2 omega x).Infinite} = ⋂ m : ℕ, zih_clusterApprox x m := by
-- proof
  apply StatMech.TwoDim.zih_clusterInfinite_eq_iInter x

/--
[zih_leftArmFrom_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_leftArmFrom_dependsOn_eq
  {x : Site 2}
  {N : ℕ} :
-- imply
  StatMech.DependsOn {omega | zfk_LeftArmFrom omega x N} (zih_leftSquareEdges N) := by
-- proof
  apply StatMech.TwoDim.zih_leftArmFrom_dependsOn x N

/--
[zih_LeftArmApprox_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_LeftArmApprox_dependsOn_eq
  {k N m : ℕ} :
-- imply
  StatMech.DependsOn (zih_LeftArmApprox k N m) (zih_leftApproxSupport k N m) := by
-- proof
  apply StatMech.TwoDim.zih_LeftArmApprox_dependsOn k N m

/--
[zih_LeftArmApprox_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_LeftArmApprox_isIncreasing_eq
  {k N m : ℕ} :
-- imply
  IsIncreasing (zih_LeftArmApprox k N m) := by
-- proof
  apply StatMech.TwoDim.zih_LeftArmApprox_isIncreasing k N m

/--
[zih_LeftArmApprox_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_LeftArmApprox_measurableSet_eq
  {k N m : ℕ} :
-- imply
  MeasurableSet (zih_LeftArmApprox k N m) := by
-- proof
  apply StatMech.TwoDim.zih_LeftArmApprox_measurableSet k N m

/--
[zih_LeftArmApprox_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_LeftArmApprox_antitone_eq
  {k N : ℕ} :
-- imply
  Antitone (zih_LeftArmApprox k N) := by
-- proof
  apply StatMech.TwoDim.zih_LeftArmApprox_antitone k N

/--
[zih_LeftArmEvent_eq_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_LeftArmEvent_eq_iInter_eq
  {k N : ℕ} :
-- imply
  zfk_LeftArmEvent k N = ⋂ m : ℕ, zih_LeftArmApprox k N m := by
-- proof
  apply StatMech.TwoDim.zih_LeftArmEvent_eq_iInter k N

/--
[zih_rightArmFrom_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_rightArmFrom_dependsOn_eq
  {y : Site 2}
  {N : ℕ} :
-- imply
  StatMech.DependsOn {omega | zfk_RightArmFrom omega y N} (zih_rightSquareEdges N) := by
-- proof
  apply StatMech.TwoDim.zih_rightArmFrom_dependsOn y N

/--
[zih_RightArmApprox_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_RightArmApprox_dependsOn_eq
  {k N m : ℕ} :
-- imply
  StatMech.DependsOn (zih_RightArmApprox k N m) (zih_rightApproxSupport k N m) := by
-- proof
  apply StatMech.TwoDim.zih_RightArmApprox_dependsOn k N m

/--
[zih_RightArmApprox_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_RightArmApprox_isIncreasing_eq
  {k N m : ℕ} :
-- imply
  IsIncreasing (zih_RightArmApprox k N m) := by
-- proof
  apply StatMech.TwoDim.zih_RightArmApprox_isIncreasing k N m

/--
[zih_RightArmApprox_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_RightArmApprox_measurableSet_eq
  {k N m : ℕ} :
-- imply
  MeasurableSet (zih_RightArmApprox k N m) := by
-- proof
  apply StatMech.TwoDim.zih_RightArmApprox_measurableSet k N m

/--
[zih_RightArmApprox_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_RightArmApprox_antitone_eq
  {k N : ℕ} :
-- imply
  Antitone (zih_RightArmApprox k N) := by
-- proof
  apply StatMech.TwoDim.zih_RightArmApprox_antitone k N

/--
[zih_RightArmEvent_eq_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_RightArmEvent_eq_iInter_eq
  {k N : ℕ} :
-- imply
  zfk_RightArmEvent k N = ⋂ m : ℕ, zih_RightArmApprox k N m := by
-- proof
  apply StatMech.TwoDim.zih_RightArmEvent_eq_iInter k N

/--
[zih_armPair_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_armPair_fkg_eq
  {k N : ℕ} :
-- imply
  halfMeasure.real (zfk_LeftArmEvent k N) * halfMeasure.real (zfk_RightArmEvent k N) ≤ halfMeasure.real (zfk_ArmPairEvent k N) := by
-- proof
  apply StatMech.TwoDim.zih_armPair_fkg k N

/--
[zih_rot_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_rot_dependsOn_eq
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
  {F : Finset (Sym2 (Site 2))}
-- given
  (hA : StatMech.DependsOn A F) :
-- imply
  StatMech.DependsOn (zrs_rot A) (zih_rotSupport F) := by
-- proof
  apply StatMech.TwoDim.zih_rot_dependsOn hA

/--
[zih_sideFamily_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_sideFamily_dependsOn_eq
  {A : Set (ConfigSpace (Sym2 (Site 2)))}
  {F : Finset (Sym2 (Site 2))}
  {i : Fin 4}
-- given
  (hA : StatMech.DependsOn A F) :
-- imply
  StatMech.DependsOn (zrs_sideFamily A i) (zih_sideSupport F i) := by
-- proof
  apply StatMech.TwoDim.zih_sideFamily_dependsOn hA i

/--
[zih_complUnion_bound_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_complUnion_bound_of_finite_dependsOn_eq
  {A B : Set (ConfigSpace (Sym2 (Site 2)))}
  {F : Finset (Sym2 (Site 2))}
-- given
  (hAdep : StatMech.DependsOn A F)
  (hBdep : StatMech.DependsOn B F)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B) :
-- imply
  (1 - halfMeasure.real A) * (1 - halfMeasure.real B) ≤ 1 - halfMeasure.real (A ∪ B) := by
-- proof
  apply StatMech.TwoDim.zih_complUnion_bound_of_finite_dependsOn F hAdep hBdep hAinc hBinc hAm hBm

/--
[zih_complUnion_four_of_finite_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_complUnion_four_of_finite_dependsOn_eq
  {A B C D : Set (ConfigSpace (Sym2 (Site 2)))}
  {F : Finset (Sym2 (Site 2))}
-- given
  (hAdep : StatMech.DependsOn A F)
  (hBdep : StatMech.DependsOn B F)
  (hCdep : StatMech.DependsOn C F)
  (hDdep : StatMech.DependsOn D F)
  (hAinc : IsIncreasing A)
  (hBinc : IsIncreasing B)
  (hCinc : IsIncreasing C)
  (hDinc : IsIncreasing D)
  (hAm : MeasurableSet A)
  (hBm : MeasurableSet B)
  (hCm : MeasurableSet C)
  (hDm : MeasurableSet D) :
-- imply
  (1 - halfMeasure.real A) * (1 - halfMeasure.real B) * (1 - halfMeasure.real C) * (1 - halfMeasure.real D) ≤ 1 - halfMeasure.real (A ∪ B ∪ C ∪ D) := by
-- proof
  apply StatMech.TwoDim.zih_complUnion_four_of_finite_dependsOn F hAdep hBdep hCdep hDdep hAinc hBinc hCinc hDinc hAm hBm hCm hDm

/--
[zih_sideApprox_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_sideApprox_antitone_eq
  {k N : ℕ}
  {i : Fin 4} :
-- imply
  Antitone (fun m => zrs_sideFamily (zih_LeftArmApprox k N m) i) := by
-- proof
  apply StatMech.TwoDim.zih_sideApprox_antitone k N i

/--
[zih_sideApprox_iInter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_sideApprox_iInter_eq
  {k N : ℕ}
  {i : Fin 4} :
-- imply
  (⋂ m, zrs_sideFamily (zih_LeftArmApprox k N m) i) = zrs_sideFamily (zfk_LeftArmEvent k N) i := by
-- proof
  apply StatMech.TwoDim.zih_sideApprox_iInter k N i

/--
[zih_complUnion_four_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_complUnion_four_left_eq
  {k N : ℕ} :
-- imply
  let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i (1 - halfMeasure.real (S 0)) * (1 - halfMeasure.real (S 1)) * (1 - halfMeasure.real (S 2)) * (1 - halfMeasure.real (S 3)) ≤ 1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3) := by
-- proof
  apply StatMech.TwoDim.zih_complUnion_four_left k N

/--
[zih_sqrt_trick_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_sqrt_trick_left_eq
  {k N : ℕ} :
-- imply
  let S := fun i : Fin 4 => zrs_sideFamily (zfk_LeftArmEvent k N) i 1 - (1 - halfMeasure.real (S 0 ∪ S 1 ∪ S 2 ∪ S 3)) ^ ((1 : ℝ) / 4) ≤ halfMeasure.real (S 0) := by
-- proof
  apply StatMech.TwoDim.zih_sqrt_trick_left k N

/--
[zih_armLower_le_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_armLower_le_left_eq
  {k N : ℕ}
-- given
  (hkN : k ≤ N) :
-- imply
  zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zih_armLower_le_left k N hkN

/--
[zih_armLower_le_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_armLower_le_right_eq
  {k N : ℕ}
-- given
  (hkN : k ≤ N) :
-- imply
  zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zih_armLower_le_right k N hkN

/--
[zih_fixedK_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_fixedK_contradiction_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2))
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  False := by
-- proof
  apply StatMech.TwoDim.zih_fixedK_contradiction hpos hhalf

/--
[zih_thetaReal_zero_of_matched_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_thetaReal_zero_of_matched_half_eq
-- given
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  halfMeasure.real (Universality.percolationEvent 2) = 0 := by
-- proof
  apply StatMech.TwoDim.zih_thetaReal_zero_of_matched_half hhalf

/--
[zih_percolationProbability_zero_of_matched_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_percolationProbability_zero_of_matched_half_eq
-- given
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zih_percolationProbability_zero_of_matched_half hhalf

/--
[zih_percolationProbability_zero_of_faithful_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_percolationProbability_zero_of_faithful_exclusive_eq
-- given
  (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
-- imply
  Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zih_percolationProbability_zero_of_faithful_exclusive hexcl

/--
[zih_criticalProbability_eq_half_of_faithful_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangHarris.lean)
-/
@[path]
private lemma zih_criticalProbability_eq_half_of_faithful_exclusive_eq
-- given
  (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  criticalProbability 2 = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.TwoDim.zih_criticalProbability_eq_half_of_faithful_exclusive hexcl hmeasGenH hmeasFace hmeasThin


-- created on 2026-10-23
