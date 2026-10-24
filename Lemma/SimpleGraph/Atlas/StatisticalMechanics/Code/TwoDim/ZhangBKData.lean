import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.TwoDim.ZhangBKData
open MeasureTheory Set Filter Topology StatMech StatMech.TwoDim


/--
[zbd_atLeastTwo_halfMeasure_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_atLeastTwo_halfMeasure_zero_eq :
-- imply
  halfMeasure (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.TwoDim.zbd_atLeastTwo_halfMeasure_zero

/--
[zbd_boxHitsInfinite_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHitsInfinite_isIncreasing_eq
  {n : ℕ} :
-- imply
  IsIncreasing (zbd_boxHitsInfinite n) := by
-- proof
  apply StatMech.TwoDim.zbd_boxHitsInfinite_isIncreasing n

/--
[zbd_boxHitsInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHitsInfinite_measurableSet_eq
  {n : ℕ} :
-- imply
  MeasurableSet (zbd_boxHitsInfinite n) := by
-- proof
  apply StatMech.TwoDim.zbd_boxHitsInfinite_measurableSet n

/--
[zbd_boxHitsInfinite_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHitsInfinite_mono_eq :
-- imply
  Monotone zbd_boxHitsInfinite := by
-- proof
  apply StatMech.TwoDim.zbd_boxHitsInfinite_mono

/--
[zbd_iUnion_boxHitsInfinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_iUnion_boxHitsInfinite_eq :
-- imply
  (⋃ n, zbd_boxHitsInfinite n) = {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} := by
-- proof
  apply StatMech.TwoDim.zbd_iUnion_boxHitsInfinite

/--
[zbd_existsInfinite_halfMeasure_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_existsInfinite_halfMeasure_one_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
-- imply
  halfMeasure {ω : ConfigSpace (Sym2 (Site 2)) | ∃ x : Site 2, (cluster 2 ω x).Infinite} = 1 := by
-- proof
  apply StatMech.TwoDim.zbd_existsInfinite_halfMeasure_one hpos

/--
[zbd_boxHit_rotated_union_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHit_rotated_union_tendsto_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
-- imply
  Tendsto (fun n => halfMeasure.real (zrs_sideFamily (zbd_boxHitsInfinite n) 0 ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 1 ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 2 ∪ zrs_sideFamily (zbd_boxHitsInfinite n) 3)) atTop (nhds 1) := by
-- proof
  apply StatMech.TwoDim.zbd_boxHit_rotated_union_tendsto hpos

/--
[zbd_connectedWithin_box_of_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_connectedWithin_box_of_connected_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hxy : Connected d omega x y) :
-- imply
  ∃ n, ∃ (hx : x ∈ box d n) (hy : y ∈ box d n), ConnectedWithin d omega (box d n) ⟨x, hx⟩ ⟨y, hy⟩ := by
-- proof
  apply StatMech.TwoDim.zbd_connectedWithin_box_of_connected omega hxy

/--
[zbd_connectedWithinBox_subset_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_connectedWithinBox_subset_connected_eq
  {d : ℕ}
  {x y : Site d}
  {n : ℕ} :
-- imply
  zbd_connectedWithinBox x y n ⊆ {omega | Connected d omega x y} := by
-- proof
  apply StatMech.TwoDim.zbd_connectedWithinBox_subset_connected x y n

/--
[zbd_iUnion_connectedWithinBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_iUnion_connectedWithinBox_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  (⋃ n, zbd_connectedWithinBox x y n) = {omega | Connected d omega x y} := by
-- proof
  apply StatMech.TwoDim.zbd_iUnion_connectedWithinBox x y

/--
[zbd_measurableSet_connectedWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_measurableSet_connectedWithin_eq
  {d : ℕ}
  {S : Set (Site d)}
  {x y : S} :
-- imply
  MeasurableSet {omega : ConfigSpace (Sym2 (Site d)) | ConnectedWithin d omega S x y} := by
-- proof
  apply StatMech.TwoDim.zbd_measurableSet_connectedWithin S x y

/--
[zbd_connectedWithinBox_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_connectedWithinBox_measurableSet_eq
  {d : ℕ}
  {x y : Site d}
  {n : ℕ} :
-- imply
  MeasurableSet (zbd_connectedWithinBox x y n) := by
-- proof
  apply StatMech.TwoDim.zbd_connectedWithinBox_measurableSet x y n

/--
[zbd_sideHasInfinite_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_sideHasInfinite_measurableSet_eq
  {d : ℕ}
  {S : Set (Site d)} :
-- imply
  MeasurableSet (zbd_sideHasInfinite S) := by
-- proof
  apply StatMech.TwoDim.zbd_sideHasInfinite_measurableSet S

/--
[zbd_sideHasInfinite_isIncreasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_sideHasInfinite_isIncreasing_eq
  {d : ℕ}
  {S : Set (Site d)} :
-- imply
  IsIncreasing (zbd_sideHasInfinite S) := by
-- proof
  apply StatMech.TwoDim.zbd_sideHasInfinite_isIncreasing S

/--
[zbd_twoScaleMerge_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScaleMerge_measurableSet_eq
  {d : ℕ}
  {L R : Set (Site d)}
  {n : ℕ} :
-- imply
  MeasurableSet (zbd_twoScaleMerge L R n) := by
-- proof
  apply StatMech.TwoDim.zbd_twoScaleMerge_measurableSet L R n

/--
[zbd_twoScaleError_measurableSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScaleError_measurableSet_eq
  {d : ℕ}
  {L R : Set (Site d)}
  {n : ℕ} :
-- imply
  MeasurableSet (zbd_twoScaleError L R n) := by
-- proof
  apply StatMech.TwoDim.zbd_twoScaleError_measurableSet L R n

/--
[zbd_connectedWithinBox_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_connectedWithinBox_mono_eq
  {d : ℕ}
  {x y : Site d} :
-- imply
  Monotone (zbd_connectedWithinBox x y) := by
-- proof
  apply StatMech.TwoDim.zbd_connectedWithinBox_mono x y

/--
[zbd_twoScaleMerge_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScaleMerge_mono_eq
  {d : ℕ}
  {L R : Set (Site d)} :
-- imply
  Monotone (zbd_twoScaleMerge L R) := by
-- proof
  apply StatMech.TwoDim.zbd_twoScaleMerge_mono L R

/--
[zbd_twoScaleError_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScaleError_antitone_eq
  {d : ℕ}
  {L R : Set (Site d)} :
-- imply
  Antitone (zbd_twoScaleError L R) := by
-- proof
  apply StatMech.TwoDim.zbd_twoScaleError_antitone L R

/--
[zbd_iInter_twoScaleError_subset_atLeastTwo](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_iInter_twoScaleError_subset_atLeastTwo_eq
  {d : ℕ}
  {L R : Set (Site d)} :
-- imply
  (⋂ n, zbd_twoScaleError L R n) ⊆ atLeastTwoInfinite d := by
-- proof
  apply StatMech.TwoDim.zbd_iInter_twoScaleError_subset_atLeastTwo L R

/--
[zbd_twoScaleError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScaleError_tendsto_zero_eq
  {L R : Set (Site 2)} :
-- imply
  Tendsto (fun n => halfMeasure.real (zbd_twoScaleError L R n)) atTop (nhds 0) := by
-- proof
  apply StatMech.TwoDim.zbd_twoScaleError_tendsto_zero L R

/--
[zbd_exists_diagonal_outerRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_exists_diagonal_outerRadius_eq
  {L R : ℕ → Set (Site 2)} :
-- imply
  ∃ M : ℕ → ℕ, (∀ n, n + 1 ≤ M n) ∧ Tendsto (fun n => halfMeasure.real (zbd_twoScaleError (L n) (R n) (M n))) atTop (nhds 0) := by
-- proof
  apply StatMech.TwoDim.zbd_exists_diagonal_outerRadius L R

/--
[zbd_twoScale_merge_cover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_twoScale_merge_cover_eq
  {d : ℕ}
  {L R : Set (Site d)}
  {n : ℕ} :
-- imply
  zbd_sideHasInfinite L ∩ zbd_sideHasInfinite R ⊆ zbd_twoScaleMerge L R n ∪ zbd_twoScaleError L R n := by
-- proof
  apply StatMech.TwoDim.zbd_twoScale_merge_cover L R n

/--
[zbd_walk_first_hit_fn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_walk_first_hit_fn_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
  {p : (openSubgraph 2 omega).Walk x y}
  {f : Site 2 → ℤ}
  {t : ℤ}
-- given
  (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
  (hx : f x < t)
  (hy : t ≤ f y) :
-- imply
  ∃ j ≤ p.length, f (p.getVert j) = t ∧ ∀ m < j, f (p.getVert m) < t := by
-- proof
  apply StatMech.TwoDim.zbd_walk_first_hit_fn p f t hstep hx hy

/--
[zbd_connectedWithin_restrict_fn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_connectedWithin_restrict_fn_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {S T : Set (Site 2)}
  {x y : Site 2}
  {f : Site 2 → ℤ}
  {t : ℤ}
-- given
  (hxS : x ∈ S)
  (hyS : y ∈ S)
  (h : ConnectedWithin 2 omega S ⟨x, hxS⟩ ⟨y, hyS⟩)
  (hstep : ∀ {u v}, (hypercubicLattice 2).Adj u v → (f u - f v).natAbs ≤ 1)
  (hx : f x < t)
  (hy : t ≤ f y)
  (hslab : ∀ z ∈ S, f z ≤ t → z ∈ T) :
-- imply
  ∃ (u : Site 2) (_ : u ∈ S), f u = t ∧ ∃ (huT : u ∈ T) (hxT : x ∈ T), ConnectedWithin 2 omega T ⟨x, hxT⟩ ⟨u, huT⟩ := by
-- proof
  apply StatMech.TwoDim.zbd_connectedWithin_restrict_fn hxS hyS h f t hstep hx hy hslab

/--
[zbd_rot_connected_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rot_connected_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2} :
-- imply
  Connected 2 (kdi_rotConfig omega) x y ↔ Connected 2 omega (rot90Inv x) (rot90Inv y) := by
-- proof
  apply StatMech.TwoDim.zbd_rot_connected_iff omega x y

/--
[zbd_rot_clusterInfinite_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rot_clusterInfinite_iff_eq
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x : Site 2} :
-- imply
  (cluster 2 (kdi_rotConfig omega) x).Infinite ↔ (cluster 2 omega (rot90Inv x)).Infinite := by
-- proof
  apply StatMech.TwoDim.zbd_rot_clusterInfinite_iff omega x

/--
[zbd_rotInv_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rotInv_sq_eq
  {x : Site 2} :
-- imply
  rot90Inv (rot90Inv x) = -x := by
-- proof
  apply StatMech.TwoDim.zbd_rotInv_sq x

/--
[zbd_rotFun_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rotFun_sq_eq
  {x : Site 2} :
-- imply
  rot90Fun (rot90Fun x) = -x := by
-- proof
  apply StatMech.TwoDim.zbd_rotFun_sq x

/--
[zbd_neg_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_neg_mem_box_eq
  {n : ℕ}
  {x : Site 2}
-- given
  (h : x ∈ box 2 n) :
-- imply
  -x ∈ box 2 n := by
-- proof
  apply StatMech.TwoDim.zbd_neg_mem_box n h

/--
[zbd_centered_opposite_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_centered_opposite_rotation_eq
  {n : ℕ} :
-- imply
  zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 = zbd_sideHasInfinite (zbd_centeredRightSide n) := by
-- proof
  apply StatMech.TwoDim.zbd_centered_opposite_rotation n

/--
[zbd_rotInv_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rotInv_cube_eq
  {x : Site 2} :
-- imply
  rot90Inv (rot90Inv (rot90Inv x)) = rot90Fun x := by
-- proof
  apply StatMech.TwoDim.zbd_rotInv_cube x

/--
[zbd_rotFun_cube](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_rotFun_cube_eq
  {x : Site 2} :
-- imply
  rot90Fun (rot90Fun (rot90Fun x)) = rot90Inv x := by
-- proof
  apply StatMech.TwoDim.zbd_rotFun_cube x

/--
[zbd_centered_top_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_centered_top_rotation_eq
  {n : ℕ} :
-- imply
  zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 = zbd_sideHasInfinite (zbd_centeredTopSide n) := by
-- proof
  apply StatMech.TwoDim.zbd_centered_top_rotation n

/--
[zbd_centered_bottom_rotation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_centered_bottom_rotation_eq
  {n : ℕ} :
-- imply
  zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3 = zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
-- proof
  apply StatMech.TwoDim.zbd_centered_bottom_rotation n

/--
[zbd_boundaryInfinite_mem_sideUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boundaryInfinite_mem_sideUnion_eq
  {n : ℕ}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {z : Site 2}
-- given
  (hzbox : z ∈ box 2 n)
  (hzinf : (cluster 2 omega z).Infinite)
  (hbd : ∃ i : Fin 2, (z i).natAbs = n) :
-- imply
  omega ∈ zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪ zbd_sideHasInfinite (zbd_centeredRightSide n) ∪ zbd_sideHasInfinite (zbd_centeredTopSide n) ∪ zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
-- proof
  apply StatMech.TwoDim.zbd_boundaryInfinite_mem_sideUnion n hzbox hzinf hbd

/--
[zbd_boxHitsInfinite_subset_centeredSideUnion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHitsInfinite_subset_centeredSideUnion_eq
  {n : ℕ} :
-- imply
  zbd_boxHitsInfinite n ⊆ zbd_sideHasInfinite (zbd_centeredLeftSide n) ∪ zbd_sideHasInfinite (zbd_centeredRightSide n) ∪ zbd_sideHasInfinite (zbd_centeredTopSide n) ∪ zbd_sideHasInfinite (zbd_centeredBottomSide n) := by
-- proof
  apply StatMech.TwoDim.zbd_boxHitsInfinite_subset_centeredSideUnion n

/--
[zbd_boxHitsInfinite_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_boxHitsInfinite_tendsto_one_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
-- imply
  Tendsto (fun n => halfMeasure.real (zbd_boxHitsInfinite n)) atTop (nhds 1) := by
-- proof
  apply StatMech.TwoDim.zbd_boxHitsInfinite_tendsto_one hpos

/--
[zbd_centeredSide_union_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_centeredSide_union_tendsto_eq
-- given
  (hpos : 0 < halfMeasure.real (Universality.percolationEvent 2)) :
-- imply
  Tendsto (fun n => halfMeasure.real (zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 0 ∪ zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 1 ∪ zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 2 ∪ zrs_sideFamily (zbd_sideHasInfinite (zbd_centeredLeftSide n)) 3)) atTop (nhds 1) := by
-- proof
  apply StatMech.TwoDim.zbd_centeredSide_union_tendsto hpos

/--
[zbd_natAbs_le_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_natAbs_le_iff_eq
  {x : ℤ}
  {n : ℕ} :
-- imply
  x.natAbs ≤ n ↔ -(n : ℤ) ≤ x ∧ x ≤ n := by
-- proof
  apply StatMech.TwoDim.zbd_natAbs_le_iff x n

/--
[zbd_mem_box_iff_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_mem_box_iff_rect_eq
  {n : ℕ}
  {x : Site 2} :
-- imply
  x ∈ box 2 n ↔ x ∈ StatMech.RSW.Box.rect (-(n : ℤ)) n (-(n : ℤ)) n := by
-- proof
  apply StatMech.TwoDim.zbd_mem_box_iff_rect n x

/--
[zbd_horizontalCrossing_of_centeredSide_connection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_horizontalCrossing_of_centeredSide_connection_eq
  {n M : ℕ}
  {omega : ConfigSpace (Sym2 (Site 2))}
  {x y : Site 2}
-- given
  (hn : 0 < n)
  (hnM : n ≤ M)
  (hx : x ∈ zbd_centeredLeftSide n)
  (hy : y ∈ zbd_centeredRightSide n)
  (hconn : ConnectedWithin 2 omega (box 2 M) ⟨x, by exact box_mono 2 hnM hx.1⟩ ⟨y, by exact box_mono 2 hnM hy.1⟩) :
-- imply
  StatMech.RSW.Box.HorizontalCrossing omega (-(n : ℤ)) n (-(M : ℤ)) M := by
-- proof
  apply StatMech.TwoDim.zbd_horizontalCrossing_of_centeredSide_connection n M hn hnM hx hy hconn

/--
[zbd_centeredMerge_subset_horizontalCrossing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/TwoDim/ZhangBKData.lean)
-/
@[path]
private lemma zbd_centeredMerge_subset_horizontalCrossing_eq
  {n M : ℕ}
-- given
  (hn : 0 < n)
  (hnM : n ≤ M) :
-- imply
  zbd_twoScaleMerge (zbd_centeredLeftSide n) (zbd_centeredRightSide n) M ⊆ StatMech.RSW.Box.horizontalCrossingEvent (-(n : ℤ)) n (-(M : ℤ)) M := by
-- proof
  apply StatMech.TwoDim.zbd_centeredMerge_subset_horizontalCrossing n M hn hnM


-- created on 2026-10-23
