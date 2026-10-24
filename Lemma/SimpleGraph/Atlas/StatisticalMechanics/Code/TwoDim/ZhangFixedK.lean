import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.ZhangFixedK
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[zfk_rot_connectedWithin_box_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rot_connectedWithin_box_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {N : ℕ}
  {x y : box 2 N} :
-- imply
  ConnectedWithin 2 (kdi_rotConfig omega) (box 2 N) x y ↔ ConnectedWithin 2 omega (box 2 N) ⟨rot90Inv x, rot90Inv_mem_box N x.2⟩ ⟨rot90Inv y, rot90Inv_mem_box N y.2⟩ := by
-- proof
  apply StatMech.TwoDim.zfk_rot_connectedWithin_box_iff omega N x y

/--
[zfk_translate_clusterInfinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_translate_clusterInfinite_iff_eq
  {t : Site 2}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2} :
-- imply
  (cluster 2 (translateConfig t omega) x).Infinite ↔ (cluster 2 omega (x + t)).Infinite := by
-- proof
  apply StatMech.TwoDim.zfk_translate_clusterInfinite_iff t omega x

/--
[zfk_connectedWithin_translate_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_connectedWithin_translate_iff_eq
  {a b c d : ℤ}
  {t : Site 2}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hx : x ∈ rect a b c d)
  (hy : y ∈ rect a b c d) :
-- imply
  ConnectedWithin 2 (translateConfig t omega) (rect a b c d) ⟨x, hx⟩ ⟨y, hy⟩ ↔ ConnectedWithin 2 omega (rect (a + t 0) (b + t 0) (c + t 1) (d + t 1)) ⟨x + t, (cti_mem_rect_translate a b c d t x).mp hx⟩ ⟨y + t, (cti_mem_rect_translate a b c d t y).mp hy⟩ := by
-- proof
  apply StatMech.TwoDim.zfk_connectedWithin_translate_iff a b c d t omega x y hx hy

/--
[zfk_shift_mem_rightSquare_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_shift_mem_rightSquare_iff_eq
  {N : ℕ}
  {x : Site 2} :
-- imply
  x ∈ zfk_leftSquare N ↔ x + (![1, 0] : Site 2) ∈ zfk_rightSquare N := by
-- proof
  apply StatMech.TwoDim.zfk_shift_mem_rightSquare_iff N x

/--
[zfk_connectedWithin_shiftRight_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_connectedWithin_shiftRight_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {N : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ zfk_leftSquare N)
  (hy : y ∈ zfk_leftSquare N) :
-- imply
  ConnectedWithin 2 (translateConfig (![1, 0] : Site 2) omega) (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔ ConnectedWithin 2 omega (zfk_rightSquare N) ⟨x + ![1, 0], (zfk_shift_mem_rightSquare_iff N x).mp hx⟩ ⟨y + ![1, 0], (zfk_shift_mem_rightSquare_iff N y).mp hy⟩ := by
-- proof
  apply StatMech.TwoDim.zfk_connectedWithin_shiftRight_iff omega N x y hx hy

/--
[zfk_rotInv_mem_leftSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotInv_mem_leftSquare_eq
  {N : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ zfk_leftSquare N) :
-- imply
  rot90Inv x ∈ zfk_leftSquare N := by
-- proof
  apply StatMech.TwoDim.zfk_rotInv_mem_leftSquare N hx

/--
[zfk_rotFun_mem_leftSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotFun_mem_leftSquare_eq
  {N : ℕ}
  {x : Site 2}
-- given
  (hx : x ∈ zfk_leftSquare N) :
-- imply
  rot90Fun x ∈ zfk_leftSquare N := by
-- proof
  apply StatMech.TwoDim.zfk_rotFun_mem_leftSquare N hx

/--
[zfk_rotInv_leftSide_mem_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotInv_leftSide_mem_topSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.leftSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Inv a ∈ StatMech.RSW.Box.topSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotInv_leftSide_mem_topSide N a

/--
[zfk_rotFun_topSide_mem_leftSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotFun_topSide_mem_leftSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.topSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Fun a ∈ StatMech.RSW.Box.leftSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotFun_topSide_mem_leftSide N a

/--
[zfk_rotInv_topSide_mem_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotInv_topSide_mem_rightSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.topSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Inv a ∈ StatMech.RSW.Box.rightSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotInv_topSide_mem_rightSide N a

/--
[zfk_rotFun_rightSide_mem_topSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotFun_rightSide_mem_topSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.rightSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Fun a ∈ StatMech.RSW.Box.topSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotFun_rightSide_mem_topSide N a

/--
[zfk_rotInv_rightSide_mem_bottomSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotInv_rightSide_mem_bottomSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.rightSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Inv a ∈ StatMech.RSW.Box.bottomSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotInv_rightSide_mem_bottomSide N a

/--
[zfk_rotFun_bottomSide_mem_rightSide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rotFun_bottomSide_mem_rightSide_eq
  {N : ℕ}
  {a : StatMech.RSW.Box.bottomSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ)} :
-- imply
  rot90Fun a ∈ StatMech.RSW.Box.rightSide (-(N : ℤ)) (N : ℤ) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_rotFun_bottomSide_mem_rightSide N a

/--
[zfk_rot_connectedWithin_leftSquare_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rot_connectedWithin_leftSquare_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {N : ℕ}
  {x y : Site 2}
-- given
  (hx : x ∈ zfk_leftSquare N)
  (hy : y ∈ zfk_leftSquare N) :
-- imply
  ConnectedWithin 2 (kdi_rotConfig omega) (zfk_leftSquare N) ⟨x, hx⟩ ⟨y, hy⟩ ↔ ConnectedWithin 2 omega (zfk_leftSquare N) ⟨rot90Inv x, zfk_rotInv_mem_leftSquare N hx⟩ ⟨rot90Inv y, zfk_rotInv_mem_leftSquare N hy⟩ := by
-- proof
  apply StatMech.TwoDim.zfk_rot_connectedWithin_leftSquare_iff omega N hx hy

/--
[zfk_rot_leftArmEvent_eq_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rot_leftArmEvent_eq_top_eq
  {k N : ℕ} :
-- imply
  zrs_rot (zfk_LeftArmEvent k N) = zfk_TopArmEvent k N := by
-- proof
  apply StatMech.TwoDim.zfk_rot_leftArmEvent_eq_top k N

/--
[zfk_rot_topArmEvent_eq_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rot_topArmEvent_eq_right_eq
  {k N : ℕ} :
-- imply
  zrs_rot (zfk_TopArmEvent k N) = zfk_CenteredRightArmEvent k N := by
-- proof
  apply StatMech.TwoDim.zfk_rot_topArmEvent_eq_right k N

/--
[zfk_rot_rightArmEvent_eq_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rot_rightArmEvent_eq_bottom_eq
  {k N : ℕ} :
-- imply
  zrs_rot (zfk_CenteredRightArmEvent k N) = zfk_BottomArmEvent k N := by
-- proof
  apply StatMech.TwoDim.zfk_rot_rightArmEvent_eq_bottom k N

/--
[zfk_boxHitsInfinite_subset_armUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_boxHitsInfinite_subset_armUnion_eq
  {k N : ℕ}
-- given
  (hkN : k ≤ N) :
-- imply
  zbd_boxHitsInfinite k ⊆ zrs_sideFamily (zfk_LeftArmEvent k N) 0 ∪ zrs_sideFamily (zfk_LeftArmEvent k N) 1 ∪ zrs_sideFamily (zfk_LeftArmEvent k N) 2 ∪ zrs_sideFamily (zfk_LeftArmEvent k N) 3 := by
-- proof
  apply StatMech.TwoDim.zfk_boxHitsInfinite_subset_armUnion k N hkN

/--
[zfk_armPair_eq_inter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armPair_eq_inter_eq
  {k N : ℕ} :
-- imply
  zfk_ArmPairEvent k N = zfk_LeftArmEvent k N ∩ zfk_RightArmEvent k N := by
-- proof
  apply StatMech.TwoDim.zfk_armPair_eq_inter k N

/--
[zfk_LeftArmEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_LeftArmEvent_isIncreasing_eq
  {k N : ℕ} :
-- imply
  IsIncreasing (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_LeftArmEvent_isIncreasing k N

/--
[zfk_RightArmEvent_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_RightArmEvent_isIncreasing_eq
  {k N : ℕ} :
-- imply
  IsIncreasing (zfk_RightArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_RightArmEvent_isIncreasing k N

/--
[zfk_LeftArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_LeftArmEvent_measurableSet_eq
  {k N : ℕ} :
-- imply
  MeasurableSet (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_LeftArmEvent_measurableSet k N

/--
[zfk_RightArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_RightArmEvent_measurableSet_eq
  {k N : ℕ} :
-- imply
  MeasurableSet (zfk_RightArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_RightArmEvent_measurableSet k N

/--
[zfk_leftSquare_subset_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_leftSquare_subset_matched_eq
  {N : ℕ} :
-- imply
  zfk_leftSquare N ⊆ zfk_matchedRect N := by
-- proof
  apply StatMech.TwoDim.zfk_leftSquare_subset_matched N

/--
[zfk_rightSquare_subset_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rightSquare_subset_matched_eq
  {N : ℕ} :
-- imply
  zfk_rightSquare N ⊆ zfk_matchedRect N := by
-- proof
  apply StatMech.TwoDim.zfk_rightSquare_subset_matched N

/--
[zfk_box_subset_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_box_subset_matched_eq
  {N : ℕ} :
-- imply
  box 2 N ⊆ zfk_matchedRect N := by
-- proof
  apply StatMech.TwoDim.zfk_box_subset_matched N

/--
[zfk_mergedArmPair_subset_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_mergedArmPair_subset_horizontalCrossing_eq
  {k N : ℕ} :
-- imply
  zfk_MergedArmPairEvent k N ⊆ StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) := by
-- proof
  apply StatMech.TwoDim.zfk_mergedArmPair_subset_horizontalCrossing k N

/--
[zfk_pairError_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_pairError_measurableSet_eq
  {x y : Site 2}
  {N : ℕ} :
-- imply
  MeasurableSet (zfk_pairError x y N) := by
-- proof
  apply StatMech.TwoDim.zfk_pairError_measurableSet x y N

/--
[zfk_pairError_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_pairError_antitone_eq
  {x y : Site 2} :
-- imply
  Antitone (zfk_pairError x y) := by
-- proof
  apply StatMech.TwoDim.zfk_pairError_antitone x y

/--
[zfk_iInter_pairError_subset_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_iInter_pairError_subset_atLeastTwo_eq
  {x y : Site 2} :
-- imply
  (⋂ N, zfk_pairError x y N) ⊆ atLeastTwoInfinite 2 := by
-- proof
  apply StatMech.TwoDim.zfk_iInter_pairError_subset_atLeastTwo x y

/--
[zfk_pairError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_pairError_tendsto_zero_eq
  {x y : Site 2} :
-- imply
  Tendsto (fun N => halfMeasure.real (zfk_pairError x y N)) atTop (nhds 0) := by
-- proof
  apply StatMech.TwoDim.zfk_pairError_tendsto_zero x y

/--
[zfk_rightCentralBox_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rightCentralBox_finite_eq
  {k : ℕ} :
-- imply
  (zfk_rightCentralBox k).Finite := by
-- proof
  apply StatMech.TwoDim.zfk_rightCentralBox_finite k

/--
[zfk_mem_leftCentralFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_mem_leftCentralFinset_eq
  {k : ℕ}
  {x : Site 2} :
-- imply
  x ∈ zfk_leftCentralFinset k ↔ x ∈ box 2 k := by
-- proof
  apply StatMech.TwoDim.zfk_mem_leftCentralFinset

/--
[zfk_mem_rightCentralFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_mem_rightCentralFinset_eq
  {k : ℕ}
  {x : Site 2} :
-- imply
  x ∈ zfk_rightCentralFinset k ↔ x ∈ zfk_rightCentralBox k := by
-- proof
  apply StatMech.TwoDim.zfk_mem_rightCentralFinset

/--
[zfk_armPair_diff_merged_subset_errorUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armPair_diff_merged_subset_errorUnion_eq
  {k N : ℕ} :
-- imply
  zfk_ArmPairEvent k N \ zfk_MergedArmPairEvent k N ⊆ zfk_pairErrorUnion k N := by
-- proof
  apply StatMech.TwoDim.zfk_armPair_diff_merged_subset_errorUnion k N

/--
[zfk_pairErrorUnion_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_pairErrorUnion_tendsto_zero_eq
  {k : ℕ} :
-- imply
  Tendsto (fun N => halfMeasure.real (zfk_pairErrorUnion k N)) atTop (nhds 0) := by
-- proof
  apply StatMech.TwoDim.zfk_pairErrorUnion_tendsto_zero k

/--
[zfk_armPair_subset_crossing_union_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armPair_subset_crossing_union_error_eq
  {k N : ℕ} :
-- imply
  zfk_ArmPairEvent k N ⊆ StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ) ∪ zfk_pairErrorUnion k N := by
-- proof
  apply StatMech.TwoDim.zfk_armPair_subset_crossing_union_error k N

/--
[zfk_armPair_probability_le_crossing_add_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armPair_probability_le_crossing_add_error_eq
  {k N : ℕ} :
-- imply
  halfMeasure.real (zfk_ArmPairEvent k N) ≤ halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) + halfMeasure.real (zfk_pairErrorUnion k N) := by
-- proof
  apply StatMech.TwoDim.zfk_armPair_probability_le_crossing_add_error k N

/--
[zfk_armPair_fkg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armPair_fkg_eq
  {k N : ℕ}
-- given
  (hpa : PositivelyAssociated halfMeasure) :
-- imply
  halfMeasure.real (zfk_LeftArmEvent k N) * halfMeasure.real (zfk_RightArmEvent k N) ≤ halfMeasure.real (zfk_ArmPairEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_armPair_fkg hpa k N

/--
[zfk_fixedK_contradiction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_fixedK_contradiction_eq
  {q : ℕ → ℝ}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hq : Tendsto q atTop (nhds 1))
  (hqnonneg : ∀ k, 0 ≤ q k)
  (hleft : ∀ k N, k + 1 ≤ N → q k ≤ halfMeasure.real (zfk_LeftArmEvent k N))
  (hright : ∀ k N, k + 1 ≤ N → q k ≤ halfMeasure.real (zfk_RightArmEvent k N))
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  False := by
-- proof
  apply StatMech.TwoDim.zfk_fixedK_contradiction hpa q hq hqnonneg hleft hright hhalf

/--
[zfk_armLower_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armLower_nonneg_eq
  {k : ℕ} :
-- imply
  0 ≤ zfk_armLower k := by
-- proof
  apply StatMech.TwoDim.zfk_armLower_nonneg k

/--
[zfk_armLower_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armLower_tendsto_one_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
-- imply
  Tendsto zfk_armLower atTop (nhds 1) := by
-- proof
  apply StatMech.TwoDim.zfk_armLower_tendsto_one hpos

/--
[zfk_armLower_le_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armLower_le_left_eq
  {k N : ℕ}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hkN : k ≤ N) :
-- imply
  zfk_armLower k ≤ halfMeasure.real (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_armLower_le_left hpa k N hkN

/--
[zfk_centeredRight_eq_rot2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_centeredRight_eq_rot2_eq
  {k N : ℕ} :
-- imply
  zfk_CenteredRightArmEvent k N = zrs_rot (zrs_rot (zfk_LeftArmEvent k N)) := by
-- proof
  apply StatMech.TwoDim.zfk_centeredRight_eq_rot2 k N

/--
[zfk_CenteredRightArmEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_CenteredRightArmEvent_measurableSet_eq
  {k N : ℕ} :
-- imply
  MeasurableSet (zfk_CenteredRightArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_CenteredRightArmEvent_measurableSet k N

/--
[zfk_centeredRight_prob_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_centeredRight_prob_eq_left_eq
  {k N : ℕ} :
-- imply
  halfMeasure.real (zfk_CenteredRightArmEvent k N) = halfMeasure.real (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_centeredRight_prob_eq_left k N

/--
[zfk_rightArmEvent_eq_translate_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_rightArmEvent_eq_translate_preimage_eq
  {k N : ℕ} :
-- imply
  zfk_RightArmEvent k N = translateConfig (![1, 0] : Site 2) ⁻¹' zfk_CenteredRightArmEvent k N := by
-- proof
  apply StatMech.TwoDim.zfk_rightArmEvent_eq_translate_preimage k N

/--
[zfk_right_prob_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_right_prob_eq_left_eq
  {k N : ℕ} :
-- imply
  halfMeasure.real (zfk_RightArmEvent k N) = halfMeasure.real (zfk_LeftArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_right_prob_eq_left k N

/--
[zfk_armLower_le_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_armLower_le_right_eq
  {k N : ℕ}
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hkN : k ≤ N) :
-- imply
  zfk_armLower k ≤ halfMeasure.real (zfk_RightArmEvent k N) := by
-- proof
  apply StatMech.TwoDim.zfk_armLower_le_right hpa k N hkN

/--
[zfk_FaithfulDualVerticalEvent_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_FaithfulDualVerticalEvent_measurableSet_eq
  {N : ℕ} :
-- imply
  MeasurableSet (zfk_FaithfulDualVerticalEvent N) := by
-- proof
  apply StatMech.TwoDim.zfk_FaithfulDualVerticalEvent_measurableSet N

/--
[zfk_faithfulDualVertical_prob_eq_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_faithfulDualVertical_prob_eq_matched_eq
  {N : ℕ} :
-- imply
  halfMeasure.real (zfk_FaithfulDualVerticalEvent N) = halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) := by
-- proof
  apply StatMech.TwoDim.zfk_faithfulDualVertical_prob_eq_matched N

/--
[zfk_matched_half_of_faithful_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_matched_half_of_faithful_exclusive_eq
  {N : ℕ}
-- given
  (hexcl : zfk_FaithfulMatchedExclusive N) :
-- imply
  halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2 := by
-- proof
  apply StatMech.TwoDim.zfk_matched_half_of_faithful_exclusive N hexcl

/--
[zfk_thetaReal_zero_of_matched_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_thetaReal_zero_of_matched_half_eq
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  halfMeasure.real (Universality.percolationEvent 2) = 0 := by
-- proof
  apply StatMech.TwoDim.zfk_thetaReal_zero_of_matched_half hpa hhalf

/--
[zfk_percolationProbability_zero_of_matched_half](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_percolationProbability_zero_of_matched_half_eq
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hhalf : ∀ N : ℕ, halfMeasure.real (StatMech.RSW.Box.horizontalCrossingEvent (-(N : ℤ)) ((N : ℤ) + 1) (-(N : ℤ)) (N : ℤ)) ≤ (1 : ℝ) / 2) :
-- imply
  Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zfk_percolationProbability_zero_of_matched_half hpa hhalf

/--
[zfk_percolationProbability_zero_of_faithful_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_percolationProbability_zero_of_faithful_exclusive_eq
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N) :
-- imply
  Universality.percolationProbability 2 (2⁻¹ : ℝ≥0) half_le_one = 0 := by
-- proof
  apply StatMech.TwoDim.zfk_percolationProbability_zero_of_faithful_exclusive hpa hexcl

/--
[zfk_criticalProbability_eq_half_of_faithful_exclusive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangFixedK.lean)
-/
@[path]
private lemma zfk_criticalProbability_eq_half_of_faithful_exclusive_eq
-- given
  (hpa : PositivelyAssociated halfMeasure)
  (hexcl : ∀ N : ℕ, zfk_FaithfulMatchedExclusive N)
  (hmeasGenH : ∀ a b : ℤ, 0 < a → 0 < b → MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent 0 a 0 b))
  (hmeasFace : ∀ n : ℤ, 0 < n → MeasurableSet (crr_FaceRectVerticalEvent n))
  (hmeasThin : ∀ n : ℤ, 0 < n → MeasurableSet (StatMech.RSW.Box.horizontalCrossingEvent (-1) n 0 (n - 1))) :
-- imply
  criticalProbability 2 = (1 : ℝ) / 2 := by
-- proof
  apply StatMech.TwoDim.zfk_criticalProbability_eq_half_of_faithful_exclusive hpa hexcl hmeasGenH hmeasFace hmeasThin


-- created on 2026-10-23
