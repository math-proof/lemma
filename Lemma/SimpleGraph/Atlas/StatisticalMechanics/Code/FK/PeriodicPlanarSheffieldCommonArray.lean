import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCommonArray.Part4
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[horizontalShift_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma horizontalShift_zero_apply_eq
  [DecidableEq V]
  [Countable V]
  {t : Int} :
-- imply
  horizontalShift t 0 = t := by
-- proof
  apply StatMech.FK.PeriodicPlanar.horizontalShift_zero_apply t

/--
[horizontalShift_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma horizontalShift_one_apply_eq
  [DecidableEq V]
  [Countable V]
  {t : Int} :
-- imply
  horizontalShift t 1 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.horizontalShift_one_apply t

/--
[boundaryGridBase_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridBase_zero_apply_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  boundaryGridBase baseLeft baseBottom 0 = baseLeft 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridBase_zero_apply baseLeft baseBottom

/--
[boundaryGridBase_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridBase_one_apply_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  boundaryGridBase baseLeft baseBottom 1 = baseBottom 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridBase_one_apply baseLeft baseBottom

/--
[boundaryGridLeftShift_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridLeftShift_zero_apply_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  boundaryGridLeftShift baseLeft baseBottom 0 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridLeftShift_zero_apply baseLeft baseBottom

/--
[boundaryGridBottomShift_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridBottomShift_one_apply_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  boundaryGridBottomShift baseLeft baseBottom 1 = 0 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridBottomShift_one_apply baseLeft baseBottom

/--
[boundaryGridRightShift_zero_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridRightShift_zero_apply_eq
  [DecidableEq V]
  [Countable V]
  {extent : Int}
  {baseRight baseBottom : Site 2} :
-- imply
  boundaryGridRightShift extent baseRight baseBottom 0 = extent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridRightShift_zero_apply extent baseRight baseBottom

/--
[boundaryGridTopShift_one_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridTopShift_one_apply_eq
  [DecidableEq V]
  [Countable V]
  {extent : Int}
  {baseLeft baseTop : Site 2} :
-- imply
  boundaryGridTopShift extent baseLeft baseTop 1 = extent := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridTopShift_one_apply extent baseLeft baseTop

/--
[boundaryGridWidth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridWidth_pos_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseLeft baseRight : Site 2}
-- given
  (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0) :
-- imply
  0 < boundaryGridWidth extent baseLeft baseRight := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridWidth_pos extent baseLeft baseRight hpos

/--
[boundaryGridHeight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGridHeight_pos_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseBottom baseTop : Site 2}
-- given
  (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1) :
-- imply
  0 < boundaryGridHeight extent baseBottom baseTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGridHeight_pos extent baseBottom baseTop hpos

/--
[boundaryGrid_left_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_left_aligned_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  baseLeft + boundaryGridLeftShift baseLeft baseBottom = boundaryGridBase baseLeft baseBottom := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_left_aligned baseLeft baseBottom

/--
[boundaryGrid_bottom_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_bottom_aligned_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2} :
-- imply
  baseBottom + boundaryGridBottomShift baseLeft baseBottom = boundaryGridBase baseLeft baseBottom := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_bottom_aligned baseLeft baseBottom

/--
[boundaryGrid_right_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_right_aligned_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseLeft baseRight baseBottom : Site 2}
-- given
  (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0) :
-- imply
  baseRight + boundaryGridRightShift extent baseRight baseBottom = boundaryGridBase baseLeft baseBottom + preferenceGridSite (Fin.last (boundaryGridWidth extent baseLeft baseRight), (0 : Fin (0 + 1))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_right_aligned extent baseLeft baseRight baseBottom hpos

/--
[boundaryGrid_top_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_top_aligned_eq
  [DecidableEq V]
  [Countable V]
  {extent : Nat}
  {baseLeft baseBottom baseTop : Site 2}
-- given
  (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1) :
-- imply
  baseTop + boundaryGridTopShift extent baseLeft baseTop = boundaryGridBase baseLeft baseBottom + preferenceGridSite ((0 : Fin (0 + 1)), Fin.last (boundaryGridHeight extent baseBottom baseTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_top_aligned extent baseLeft baseBottom baseTop hpos

/--
[boundaryGrid_bottom_row_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_bottom_row_aligned_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2}
  {i : Fin (width + 1)}
-- given
  (width height : Nat) :
-- imply
  baseBottom + boundaryGridBottomShift baseLeft baseBottom + horizontalShift i.val = boundaryGridBase baseLeft baseBottom + preferenceGridSite (i, (0 : Fin (height + 1))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_bottom_row_aligned width height baseLeft baseBottom i

/--
[boundaryGrid_left_column_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_left_column_aligned_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseBottom : Site 2}
  {j : Fin (height + 1)}
-- given
  (width height : Nat) :
-- imply
  baseLeft + boundaryGridLeftShift baseLeft baseBottom + verticalShift j.val = boundaryGridBase baseLeft baseBottom + preferenceGridSite ((0 : Fin (width + 1)), j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_left_column_aligned width height baseLeft baseBottom j

/--
[boundaryGrid_right_column_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_right_column_aligned_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseRight baseBottom : Site 2}
  {j : Fin (height + 1)}
-- given
  (extent height : Nat)
  (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0) :
-- imply
  baseRight + boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val = boundaryGridBase baseLeft baseBottom + preferenceGridSite (Fin.last (boundaryGridWidth extent baseLeft baseRight), j) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_right_column_aligned extent height baseLeft baseRight baseBottom hpos j

/--
[boundaryGrid_top_row_aligned](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma boundaryGrid_top_row_aligned_eq
  [DecidableEq V]
  [Countable V]
  {extent width : Nat}
  {baseLeft baseBottom baseTop : Site 2}
  {i : Fin (width + 1)}
-- given
  (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1) :
-- imply
  baseTop + boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val = boundaryGridBase baseLeft baseBottom + preferenceGridSite (i, Fin.last (boundaryGridHeight extent baseBottom baseTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.boundaryGrid_top_row_aligned extent width baseLeft baseBottom baseTop hpos i

/--
[PeriodicPlaneEmbedding.rectBottomConnection_boundaryGrid_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma rectBottomConnection_boundaryGrid_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {baseLeft baseBottom : Site 2}
  {i : Fin (width + 1)}
  {a b c d a' b' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (ha : a' ≤ a + ((boundaryGridBottomShift baseLeft baseBottom + horizontalShift i.val) 0 : Int))
  (hb : b + ((boundaryGridBottomShift baseLeft baseBottom + horizontalShift i.val) 0 : Int) ≤ b')
  (hd : d + ((boundaryGridBottomShift baseLeft baseBottom + horizontalShift i.val) 1 : Int) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (P.shift baseBottom '' S) (E.rectBottomBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c d' (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite (i, (0 : Fin (height + 1)))) '' S) (E.rectBottomBoundaryVertices a' b' c d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectBottomConnection_boundaryGrid_measureReal_le E mu hTI width height baseLeft baseBottom i a b c d a' b' d' S ha hb hd

/--
[PeriodicPlaneEmbedding.rectLeftConnection_boundaryGrid_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma rectLeftConnection_boundaryGrid_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {baseLeft baseBottom : Site 2}
  {j : Fin (height + 1)}
  {a b c d b' c' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (width height : Nat)
  (hb : b + ((boundaryGridLeftShift baseLeft baseBottom + verticalShift j.val) 0 : Int) ≤ b')
  (hc : c' ≤ c + ((boundaryGridLeftShift baseLeft baseBottom + verticalShift j.val) 1 : Int))
  (hd : d + ((boundaryGridLeftShift baseLeft baseBottom + verticalShift j.val) 1 : Int) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (P.shift baseLeft '' S) (E.rectLeftBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a b' c' d' (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite ((0 : Fin (width + 1)), j)) '' S) (E.rectLeftBoundaryVertices a b' c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectLeftConnection_boundaryGrid_measureReal_le E mu hTI width height baseLeft baseBottom j a b c d b' c' d' S hb hc hd

/--
[PeriodicPlaneEmbedding.rectRightConnection_boundaryGrid_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma rectRightConnection_boundaryGrid_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {baseLeft baseRight baseBottom : Site 2}
  {j : Fin (height + 1)}
  {a b c d a' c' d' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (extent height : Nat)
  (hpos : 0 < baseRight 0 + (extent : Int) - baseLeft 0)
  (ha : a' ≤ a + ((boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val) 0 : Int))
  (hc : c' ≤ c + ((boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val) 1 : Int))
  (hd : d + ((boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val) 1 : Int) ≤ d') :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (P.shift baseRight '' S) (E.rectRightBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' (b + ((boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val) 0 : Int)) c' d' (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite (Fin.last (boundaryGridWidth extent baseLeft baseRight), j)) '' S) (E.rectRightBoundaryVertices a' (b + ((boundaryGridRightShift extent baseRight baseBottom + verticalShift j.val) 0 : Int)) c' d')) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectRightConnection_boundaryGrid_measureReal_le E mu hTI extent height baseLeft baseRight baseBottom hpos j a b c d a' c' d' S ha hc hd

/--
[PeriodicPlaneEmbedding.rectTopConnection_boundaryGrid_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma rectTopConnection_boundaryGrid_measureReal_le_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsFiniteMeasure mu]
  {extent width : Nat}
  {baseLeft baseBottom baseTop : Site 2}
  {i : Fin (width + 1)}
  {a b c d a' b' c' : Real}
  {S : Set V}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hpos : 0 < baseTop 1 + (extent : Int) - baseBottom 1)
  (ha : a' ≤ a + ((boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val) 0 : Int))
  (hb : b + ((boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val) 0 : Int) ≤ b')
  (hc : c' ≤ c + ((boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val) 1 : Int)) :
-- imply
  mu.real (E.rectSideConnectionEvent a b c d (P.shift baseTop '' S) (E.rectTopBoundaryVertices a b c d)) ≤ mu.real (E.rectSideConnectionEvent a' b' c' (d + ((boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val) 1 : Int)) (P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite (i, Fin.last (boundaryGridHeight extent baseBottom baseTop))) '' S) (E.rectTopBoundaryVertices a' b' c' (d + ((boundaryGridTopShift extent baseLeft baseTop + horizontalShift i.val) 1 : Int)))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.rectTopConnection_boundaryGrid_measureReal_le E mu hTI extent width baseLeft baseBottom baseTop hpos i a b c d a' b' c' S ha hb hc

/--
[PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_corners](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma preferenceGrid_translatedSet_subset_rect_of_corners_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {width height : Nat}
  {base : Site 2}
  {S : Set V}
  {a b c d : Real}
-- given
  (hleft : ∀ u ∈ S, a ≤ E.vertexCoord (P.shift base u) 0)
  (hright : ∀ u ∈ S, E.vertexCoord (P.shift (base + preferenceGridSite (Fin.last width, (0 : Fin (0 + 1)))) u) 0 ≤ b)
  (hbottom : ∀ u ∈ S, c ≤ E.vertexCoord (P.shift base u) 1)
  (htop : ∀ u ∈ S, E.vertexCoord (P.shift (base + preferenceGridSite ((0 : Fin (0 + 1)), Fin.last height)) u) 1 ≤ d) :
-- imply
  ∀ v : PreferenceGridVertex width height, P.shift (base + preferenceGridSite v) '' S ⊆ E.rectVertices a b c d := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_corners E base S a b c d hleft hright hbottom htop

/--
[PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_commonSquare](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma preferenceGrid_translatedSet_subset_rect_of_commonSquare_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {M extentX extentY : Nat}
  {baseLeft baseRight baseBottom baseTop : Site 2}
  {S : Set V}
-- given
  (hposX : 0 < baseRight 0 + (extentX : Int) - baseLeft 0)
  (hposY : 0 < baseTop 1 + (extentY : Int) - baseBottom 1)
  (hleft : P.shift baseLeft '' S ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (hright : P.shift baseRight '' S ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (hbottom : P.shift baseBottom '' S ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real))
  (htop : P.shift baseTop '' S ⊆ E.rectVertices (-(M : Real)) (M : Real) (-(M : Real)) (M : Real)) :
-- imply
  ∀ v : PreferenceGridVertex (boundaryGridWidth extentX baseLeft baseRight) (boundaryGridHeight extentY baseBottom baseTop), P.shift (boundaryGridBase baseLeft baseBottom + preferenceGridSite v) '' S ⊆ E.rectVertices (-(M : Real)) (M + extentX : Real) (-(M : Real)) (M + extentY : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.preferenceGrid_translatedSet_subset_rect_of_commonSquare E M extentX extentY baseLeft baseRight baseBottom baseTop hposX hposY S hleft hright hbottom htop

/--
[exists_deep_common_preference_grid_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma exists_deep_common_preference_grid_witness_eq
  [DecidableEq V]
  [Countable V]
  {width height margin : Nat}
-- given
  (hwidth : 0 < width)
  (vertical horizontal : PreferenceGridVertex width height → Bool)
  (hverticalBottom : ∀ v, v.2.val ≤ margin → vertical v = true)
  (hverticalTop : ∀ v, height ≤ v.2.val + margin → vertical v = false)
  (hhorizontalLeft : ∀ v, v.1.val ≤ margin → horizontal v = true)
  (hhorizontalRight : ∀ v, width ≤ v.1.val + margin → horizontal v = false) :
-- imply
  ∃ x xVertical xHorizontal : PreferenceGridVertex width height, vertical x = true ∧ horizontal x = true ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) ∧ vertical xVertical = false ∧ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) ∧ horizontal xHorizontal = false ∧ margin ≤ x.1.val ∧ x.1.val + margin < width ∧ margin ≤ x.2.val ∧ x.2.val + margin < height := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_deep_common_preference_grid_witness hwidth vertical horizontal hverticalBottom hverticalTop hhorizontalLeft hhorizontalRight

/--
[PeriodicPlaneEmbedding.exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1) :
-- imply
  ∃ radius : Nat → Nat, ∀ (width height margin : Nat → Nat) (hwidth : ∀ n, 0 < width n) (base : Nat → Site 2) (vertical horizontal : (n : Nat) → PreferenceGridVertex (width n) (height n) → Bool) (a b c d : Nat → Real), (∀ n (v : PreferenceGridVertex (width n) (height n)), margin n ≤ v.1.val → v.1.val + margin n < width n → margin n ≤ v.2.val → v.2.val + margin n < height n → (P.shift (base n + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) ⊆ E.rectVertices (a n) (b n) (c n) (d n)) → (∀ n v, v.2.val ≤ margin n → vertical n v = true) → (∀ n v, height n ≤ v.2.val + margin n → vertical n v = false) → (∀ n v, v.1.val ≤ margin n → horizontal n v = true) → (∀ n v, width n ≤ v.1.val + margin n → horizontal n v = false) → (∀ n v, vertical n v = true → E.BottomPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) → (∀ n v, vertical n v = false → E.TopPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) → (∀ n v, horizontal n v = true → E.LeftPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) → (∀ n v, horizontal n v = false → E.RightPreferred mu n (a n) (b n) (c n) (d n) (base n + preferenceGridSite v)) → Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) (mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformRadius_deepGridPreference_crossing_max_tendsto_one E mu hFKG hTI hunique

/--
[exists_commonPreferenceExtents_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma exists_commonPreferenceExtents_ge_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseRight baseBottom baseTop : Site 2}
  {baseLeftDual baseRightDual baseBottomDual baseTopDual : Site 2}
  {minimumX minimumY : Nat} :
-- imply
  ∃ extentX extentY : Nat, minimumX ≤ extentX ∧ minimumY ≤ extentY ∧ 0 < baseRight 0 + (extentX : Int) - baseLeft 0 ∧ 0 < baseRightDual 0 + (extentX : Int) - baseLeftDual 0 ∧ 0 < baseTop 1 + (extentY : Int) - baseBottom 1 ∧ 0 < baseTopDual 1 + (extentY : Int) - baseBottomDual 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_commonPreferenceExtents_ge baseLeft baseRight baseBottom baseTop baseLeftDual baseRightDual baseBottomDual baseTopDual minimumX minimumY

/--
[exists_commonPositivePreferenceExtents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldCommonArray.lean)
-/
@[path]
private lemma exists_commonPositivePreferenceExtents_eq
  [DecidableEq V]
  [Countable V]
  {baseLeft baseRight baseBottom baseTop : Site 2}
  {baseLeftDual baseRightDual baseBottomDual baseTopDual : Site 2} :
-- imply
  ∃ extentX extentY : Nat, 0 < baseRight 0 + (extentX : Int) - baseLeft 0 ∧ 0 < baseRightDual 0 + (extentX : Int) - baseLeftDual 0 ∧ 0 < baseTop 1 + (extentY : Int) - baseBottom 1 ∧ 0 < baseTopDual 1 + (extentY : Int) - baseBottomDual 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_commonPositivePreferenceExtents baseLeft baseRight baseBottom baseTop baseLeftDual baseRightDual baseBottomDual baseTopDual


-- created on 2026-10-23
