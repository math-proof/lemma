import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalRadialPatch.Part15
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchHalf_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHalf_eq_eq
  {i j : Nat} :
-- imply
  fkIsingSquareRadialPatchHalf i j = (i + j + 1) / 2 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHalf_eq i j

/--
[fkIsingSquareRadialPatchDirection_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDirection_available_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hm : m ≤ n) :
-- imply
  fkIsingSquareDirectionAvailable n (fkIsingSquareRadialPatchVertex n m hm i j) (fkIsingSquareRadialPatchDirection i.1 j.1) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDirection_available n m hm i j

/--
[fkIsingSquareRadialPatchEdge_orientation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchEdge_orientation_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hm : m ≤ n) :
-- imply
  fkIsingSquareOrientedEdge n (fkIsingSquareRadialPatchEdge n m hm i j) = fkIsingSquareDirectionEdgeOrientation n (fkIsingSquareRadialPatchVertex n m hm i j) (fkIsingSquareRadialPatchDirection i.1 j.1) (fkIsingSquareRadialPatchDirection_available n m hm i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchEdge_orientation n m hm i j

/--
[fkIsingSquareRadialPatchEdge_eq_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchEdge_eq_east_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hm : m ≤ n)
  (heven : Even (i.1 + j.1)) :
-- imply
  fkIsingSquareRadialPatchEdge n m hm i j = fkIsingSquareDirectionEdge n (fkIsingSquareRadialPatchVertex n m hm i j) .east (by simpa [fkIsingSquareRadialPatchDirection, heven] using fkIsingSquareRadialPatchDirection_available n m hm i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchEdge_eq_east n m hm i j heven

/--
[fkIsingSquareRadialPatchEdge_eq_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchEdge_eq_north_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hm : m ≤ n)
  (hodd : ¬ Even (i.1 + j.1)) :
-- imply
  fkIsingSquareRadialPatchEdge n m hm i j = fkIsingSquareDirectionEdge n (fkIsingSquareRadialPatchVertex n m hm i j) .north (by simpa [fkIsingSquareRadialPatchDirection, hodd] using fkIsingSquareRadialPatchDirection_available n m hm i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchEdge_eq_north n m hm i j hodd

/--
[fkIsingSquareDartEndpoint_directionEdge_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_directionEdge_east_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .east) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareDirectionEdge n u .east hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_directionEdge_east n u hu s

/--
[fkIsingSquareDartDirection_directionEdge_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_directionEdge_east_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .east) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareDirectionEdge n u .east hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_directionEdge_east n u hu s

/--
[fkIsingSquareDartEndpoint_directionEdge_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_directionEdge_north_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .north) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareDirectionEdge n u .north hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_directionEdge_north n u hu s

/--
[fkIsingSquareDartDirection_directionEdge_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_directionEdge_north_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .north) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareDirectionEdge n u .north hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_directionEdge_north n u hu s

/--
[fkIsingSquareDartEndpoint_directionEdge_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartEndpoint_directionEdge_south_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .south) :
-- imply
  fkIsingSquareDartEndpoint n (fkIsingSquareDirectionEdge n u .south hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartEndpoint_directionEdge_south n u hu s

/--
[fkIsingSquareDartDirection_directionEdge_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareDartDirection_directionEdge_south_eq
  {n : Nat}
  {u : (fkSquareBoxPlanar n).V}
  {s : FKIsingMedialSide}
-- given
  (hu : fkIsingSquareDirectionAvailable n u .south) :
-- imply
  fkIsingSquareDartDirection n (fkIsingSquareDirectionEdge n u .south hu, s) = match (fkIsingSquareSideCorner s).1 with := by
-- proof
  apply StatMech.Universality.fkIsingSquareDartDirection_directionEdge_south n u hu s

/--
[fkIsingSquareRadialPatchWedgeFaceKey_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWedgeFaceKey_of_even_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hm : m ≤ n)
  (heven : Even (i.1 + j.1)) :
-- imply
  fkIsingSquareWedgeFaceKey n (fkIsingSquareRadialPatchEdge n m hm i j, s) = match s with | .west := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWedgeFaceKey_of_even n m hm i j heven s

/--
[fkIsingSquareRadialPatchWedgeFaceKey_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchWedgeFaceKey_of_odd_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hm : m ≤ n)
  (hodd : ¬ Even (i.1 + j.1)) :
-- imply
  fkIsingSquareWedgeFaceKey n (fkIsingSquareRadialPatchEdge n m hm i j, s) = match s with | .west := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchWedgeFaceKey_of_odd n m hm i j hodd s

/--
[fkIsingSquareRadialPatch_bondMate_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_bondMate_right_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchRightSide i j) = (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_bondMate_right n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j s) = Complex.normSq (isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareWiredFullMedialObservable n hn (fkIsingSquareRadialPatchEdge n m hm i j))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchIncidence_increment_eq_normSq_full_projection n m hn hm i j s

/--
[fkIsingSquareRadialPatchFullObservable_projection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservable_projection_eq
  {n m : Nat}
  {i j : Fin m}
  {s : FKIsingMedialSide}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  isingProj (fkIsingSquareWiredDirectedTangent n hn (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s))) (fkIsingSquareRadialPatchFullObservable n m hn hm i j) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm i j, s)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservable_projection n m hn hm i j s

/--
[fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j) = fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j (fkIsingSquareRadialPatchBottomSide i j)) + fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j (fkIsingSquareRadialPatchTopSide i j)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_normSq_full_eq_bottom_add_top_increment n m hn hm i j

/--
[fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment_eq
  {n m : Nat}
  {i j : Fin m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n) :
-- imply
  Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm i j) = fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j (fkIsingSquareRadialPatchLeftSide i j)) + fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchIncidence n m hn hm i j (fkIsingSquareRadialPatchRightSide i j)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_normSq_full_eq_left_add_right_increment n m hn hm i j

/--
[fkIsingSquareRadialPatchIncidence_right_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchIncidence_right_eq_left_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, by omega⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchRightSide i j) = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i + 1, hi⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchLeftSide (i + 1) j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchIncidence_right_eq_left n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatch_bondMate_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_bondMate_top_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  fkIsingSquareBondMate n hn (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩, fkIsingSquareRadialPatchTopSide i j) = (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩, fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_bondMate_top n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatch_directedTangentCode_right_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_directedTangentCode_right_modEq_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchLeftSide (i + 1) j)) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchRightSide i j)) [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_directedTangentCode_right_modEq n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatch_directedTangentCode_top_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_directedTangentCode_top_modEq_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩, fkIsingSquareRadialPatchBottomSide i (j + 1))) ≡ fkIsingSquareWiredDirectedTangentCode n hn (.bond (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩, fkIsingSquareRadialPatchTopSide i j)) [ZMOD 8] := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_directedTangentCode_top_modEq n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatch_fermionicObservable_right_eq_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_fermionicObservable_right_eq_left_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj : j < m) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, by omega⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchRightSide i j)) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i + 1, hi⟩ ⟨j, hj⟩, fkIsingSquareRadialPatchLeftSide (i + 1) j)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_fermionicObservable_right_eq_left n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j, by omega⟩, fkIsingSquareRadialPatchTopSide i j)) = (fkIsingSquareWiredDobrushinDomain n hn).fermionicObservable (.dart (fkIsingSquareRadialPatchEdge n m hm ⟨i, hi⟩ ⟨j + 1, hj⟩, fkIsingSquareRadialPatchBottomSide i (j + 1))) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_fermionicObservable_top_eq_bottom n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatchFullObservable_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservable_quad_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservable_quad n m i j hn hm hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchFullObservable_quad_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchFullObservable_quad_of_odd_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  IsingSquareSHolomorphicQuad (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchFullObservable_quad_of_odd n m i j hn hm hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareRadialPatchIncidence_top_eq_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchIncidence_top_eq_bottom_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hi : i < m)
  (hj : j + 1 < m) :
-- imply
  fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, by omega⟩ (fkIsingSquareRadialPatchTopSide i j) = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j + 1, hj⟩ (fkIsingSquareRadialPatchBottomSide i (j + 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchIncidence_top_eq_bottom n m hn hm i j hi hj

/--
[fkIsingSquareRadialPatchHorizontalIncidence_bottom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontalIncidence_bottom_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchBottomSide i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontalIncidence_bottom n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchHorizontalIncidence_top](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontalIncidence_top_eq
  {n m : Nat}
  {i : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m) :
-- imply
  fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i m = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ (fkIsingSquareRadialPatchLast m hmpos) (fkIsingSquareRadialPatchTopSide i (m - 1)) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontalIncidence_top n m hn hm hmpos i hi

/--
[fkIsingSquareRadialPatchVerticalIncidence_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVerticalIncidence_left_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchLeftSide i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVerticalIncidence_left n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchVerticalIncidence_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVerticalIncidence_right_eq
  {n m : Nat}
  {j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos m j = fkIsingSquareRadialPatchIncidence n m hn hm (fkIsingSquareRadialPatchLast m hmpos) ⟨j, hj⟩ (fkIsingSquareRadialPatchRightSide (m - 1) j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVerticalIncidence_right n m hn hm hmpos j hj

/--
[fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i (j + 1) = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchTopSide i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchHorizontalIncidence_top_of_cell n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchVerticalIncidence_right_of_cell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVerticalIncidence_right_of_cell_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos (i + 1) j = fkIsingSquareRadialPatchIncidence n m hn hm ⟨i, hi⟩ ⟨j, hj⟩ (fkIsingSquareRadialPatchRightSide i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVerticalIncidence_right_of_cell n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchSignedIncrement_closed_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchSignedIncrement_closed_on_eq
  {n m : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  IsingRectangleClosedOneFormOn (fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos) (fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos) m m := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchSignedIncrement_closed_on n m hn hm hmpos

/--
[fkIsingSquareRadialPatchPrimitive_horizontal_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_horizontal_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j ≤ m) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j = fkIsingSquareRadialPatchHorizontalSignedIncrement n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_horizontal_increment n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchPrimitive_vertical_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_vertical_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j = fkIsingSquareRadialPatchVerticalSignedIncrement n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_vertical_increment n m hn hm hmpos i j

/--
[fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j ≤ m) :
-- imply
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| = fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchHorizontalIncidence n m hn hm hmpos i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_abs_horizontal_sub_eq_increment n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| = fkIsingSquareInteriorRadialIncrement n hn (fkIsingSquareRadialPatchVerticalIncidence n m hn hm hmpos i j) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_abs_vertical_sub_eq_increment n m hn hm hmpos i j

/--
[fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m) :
-- imply
  2 * Complex.normSq (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, hi⟩ ⟨j, hj⟩) = |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| + |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1)| + |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j| + |fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) (j + 1) - fkIsingSquareRadialPatchPrimitive n m hn hm hmpos (i + 1) j| := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_two_mul_normSq_full_eq_cell_totalVariation n m hn hm hmpos i j hi hj

/--
[fkIsingSquareRadialPatchPrimalNodeVertex_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalNodeVertex_injective_eq
  {n m : Nat}
-- given
  (hm : m ≤ n) :
-- imply
  Function.Injective (fkIsingSquareRadialPatchPrimalNodeVertex n m hm) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalNodeVertex_injective n m hm

/--
[fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east_eq
  {n m i j : Nat}
-- given
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j + 1, hj⟩ = fkIsingSquareNeighbor n (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) .east (by have h := fkIsingSquareRadialPatchDirection_available n m hm ⟨i, by omega⟩ ⟨j, by omega⟩ simpa [fkIsingSquareRadialPatchDirection, heven] using h) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertex_northeast_eq_neighbor_east n m i j hm hi hj heven

/--
[fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north_eq
  {n m i j : Nat}
-- given
  (hm : m ≤ n)
  (hi : i + 1 < m)
  (hj0 : 0 < j)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi⟩ ⟨j - 1, by omega⟩ = fkIsingSquareNeighbor n (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) .north (by simp [fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf] have hmod := Nat.even_iff.mp heven omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertex_northwest_eq_neighbor_north n m i j hm hi hj0 hj heven

/--
[fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west_eq
  {n m i j : Nat}
-- given
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hj0 : 0 < j)
  (hi : i < m)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ = fkIsingSquareNeighbor n (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩) .west (by simp [fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf] have hmod := Nat.even_iff.mp heven omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertex_southwest_eq_neighbor_west n m i j hm hi0 hj0 hi hj heven

/--
[fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south_eq
  {n m i j : Nat}
-- given
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hj : j + 1 < m)
  (hi : i < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j + 1, hj⟩ = fkIsingSquareNeighbor n (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, by omega⟩) .south (by simp [fkIsingSquareDirectionAvailable, fkIsingSquareRadialPatchVertex, fkIsingSquareRadialPatchHalf] have hmod := Nat.even_iff.mp heven omega) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchVertex_southeast_eq_neighbor_south n m i j hm hi0 hj hi heven

/--
[fkIsingSquareRadialPatch_adj_iff_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_adj_iff_diagonal_eq
  {n m i j : Nat}
  {y : (fkSquareBoxPlanar n).V}
-- given
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  (fkSquareBoxPlanar n).G.Adj (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) y ↔ y = fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩ ∨ y = fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩ ∨ y = fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩ ∨ y = fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩ := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_adj_iff_diagonal n m i j hm hi0 hi1 hj0 hj1 heven y

/--
[fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j = fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_divergence n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j = -fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_eq_neg_divergence_of_odd n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j = isingPrimalProjectionDivergence (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_projectionDivergence n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j = isingPrimalProjectionDivergence (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_rotated_projectionDivergence_of_odd n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j = isingPrimalPrimitiveLaplacian (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalIncrementDivergence_eq_primitiveLaplacian n m i j hn hm hmpos hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd_eq
  {n m i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (hodd : ¬ Even (i + j)) :
-- imply
  0 ≤ fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_diagonalLaplacian_nonneg_of_odd n m i j hn hm hmpos hi0 hi1 hj0 hj1 hodd

/--
[fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal_eq
  {n m i j : Nat}
  {f : (fkSquareBoxPlanar n).V → Real}
  {H : Nat → Nat → Real}
-- given
  (hm : m ≤ n)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j))
  (hc : f (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) = H i j)
  (hne : f (fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi1⟩ ⟨j + 1, hj1⟩) = H (i + 1) (j + 1))
  (hnw : f (fkIsingSquareRadialPatchVertex n m hm ⟨i + 1, hi1⟩ ⟨j - 1, by omega⟩) = H (i + 1) (j - 1))
  (hsw : f (fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩) = H (i - 1) (j - 1))
  (hse : f (fkIsingSquareRadialPatchVertex n m hm ⟨i - 1, by omega⟩ ⟨j + 1, hj1⟩) = H (i - 1) (j + 1)) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G f (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) = fkIsingSquareRadialPatchDiagonalLaplacian H i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatch_finiteGraphLaplacian_eq_diagonal n m i j hm hi0 hi1 hj0 hj1 heven f H hc hne hnw hsw hse

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_eq
  {n m : Nat}
  {base : Real}
  {p : FKIsingSquareRadialPatchPrimalNode m}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base (fkIsingSquareRadialPatchPrimalNodeVertex n m hm p) = base + fkIsingSquareRadialPatchPrimitive n m hn hm hmpos p.1.1.1 p.1.2.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply n m hn hm hmpos base p

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even_eq
  {n m : Nat}
  {base : Real}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi : i < m)
  (hj : j < m)
  (heven : Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base (fkIsingSquareRadialPatchVertex n m hm ⟨i, hi⟩ ⟨j, hj⟩) = base + fkIsingSquareRadialPatchPrimitive n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_apply_of_even n m hn hm hmpos base i j hi hj heven

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base) (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) = fkIsingSquareRadialPatchDiagonalLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_diagonal n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base) (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) = fkIsingSquareRadialPatchPrimalIncrementDivergence n m hn hm hmpos i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_eq_divergence n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonneg_of_quad](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonneg_of_quad_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j))
  (hquad : IsingSquareSHolomorphicQuad (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j - 1, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j, by omega⟩) (fkIsingSquareRadialPatchFullObservable n m hn hm ⟨i - 1, by omega⟩ ⟨j - 1, by omega⟩)) :
-- imply
  0 ≤ isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base) (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonneg_of_quad n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven hquad

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos_eq
  {n m i j : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 < m)
  (hj0 : 0 < j)
  (hj1 : j + 1 < m)
  (heven : Even (i + j)) :
-- imply
  isingFiniteGraphLaplacian (fkSquareBoxPlanar n).G (fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base) (fkIsingSquareRadialPatchVertex n m hm ⟨i, by omega⟩ ⟨j, by omega⟩) ≤ 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_laplacian_nonpos n m i j hn hm hmpos base hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimalPrimitiveExtension_superharmonicOn_region](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimalPrimitiveExtension_superharmonicOn_region_eq
  {n m : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m) :
-- imply
  IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fun x ↦ ¬ fkIsingSquareRadialPatchInteriorEvenRegion n m hm x) (fkIsingSquareRadialPatchPrimalPrimitiveExtension n m hn hm hmpos base) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimalPrimitiveExtension_superharmonicOn_region n m hn hm hmpos base

/--
[fkIsingSquareGrowingRadialPrimalPrimitive_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareGrowingRadialPrimalPrimitive_apply_eq
  {m : Nat → Nat}
  {base : Nat → Real}
  {n : Nat}
  {p : FKIsingSquareRadialPatchPrimalNode (m n)}
-- given
  (hm : ∀ n, m n ≤ n)
  (hmn : 0 < m n) :
-- imply
  fkIsingSquareGrowingRadialPrimalPrimitive m hm base n (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p) = base n + fkIsingSquareRadialPatchPrimitive n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn p.1.1.1 p.1.2.1 := by
-- proof
  apply StatMech.Universality.fkIsingSquareGrowingRadialPrimalPrimitive_apply m hm base n hmn p

/--
[fkIsingSquareRadialPatchPrimitive_uniform_convergence_to_imPhi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_uniform_convergence_to_imPhi_eq
  {Phi : Complex → Complex}
  {eps : Nat → Real}
  {m : Nat → Nat}
  {base : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (upper lower harmonic physical : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hm : ∀ n, m n ≤ n)
  (hmpos : ∀ᶠ n in atTop, 0 < m n)
  (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
  (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → upper n x ≤ harmonic n x + eps n)
  (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → harmonic n x ≤ lower n x + eps n)
  (hsandwich : ∀ n x, lower n x ≤ physical n x ∧ physical n x ≤ upper n x)
  (heps : Tendsto eps atTop (nhds 0))
  (hdirichlet : ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| < eta)
  (hidentify : ∀ n (hn : 0 < n) (hmn : 0 < m n) (i j : Fin (m n)), Even (i.1 + j.1) → base n + fkIsingSquareRadialPatchPrimitive n (m n) hn (hm n) hmn i.1 j.1 = physical n (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ (hmn : 0 < m n) (i j : Fin (m n)), Even (i.1 + j.1) → |base n + fkIsingSquareRadialPatchPrimitive n (m n) (lt_of_lt_of_le hmn (hm n)) (hm n) hmn i.1 j.1 - fkIsingSquareSampledImaginaryPart embedding Phi n (fkIsingSquareRadialPatchVertex n (m n) (hm n) i j)| < eta := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_uniform_convergence_to_imPhi embedding Phi upper lower harmonic physical eps m base hm hmpos hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich heps hdirichlet hidentify

/--
[fkIsingSquareGrowingRadialPrimalPrimitive_uniform_convergence_to_imPhi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareGrowingRadialPrimalPrimitive_uniform_convergence_to_imPhi_eq
  {Phi : Complex → Complex}
  {eps : Nat → Real}
  {m : Nat → Nat}
  {base : Nat → Real}
-- given
  (embedding : ∀ n, (fkSquareBoxPlanar n).V → Complex)
  (upper lower harmonic : ∀ n, (fkSquareBoxPlanar n).V → Real)
  (hm : ∀ n, m n ≤ n)
  (hmpos : ∀ᶠ n in atTop, 0 < m n)
  (hupper : ∀ n, IsingFiniteGraphSubharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (upper n))
  (hlower : ∀ n, IsingFiniteGraphSuperharmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (lower n))
  (hharmonic : ∀ n, IsingFiniteGraphHarmonicOn (fkSquareBoxPlanar n).G (fkIsingSquareBoxBoundary n) (harmonic n))
  (hupperBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → upper n x ≤ harmonic n x + eps n)
  (hlowerBoundary : ∀ n x, fkIsingSquareBoxBoundary n x → harmonic n x ≤ lower n x + eps n)
  (hsandwich : ∀ n x, lower n x ≤ fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ∧ fkIsingSquareGrowingRadialPrimalPrimitive m hm base n x ≤ upper n x)
  (heps : Tendsto eps atTop (nhds 0))
  (hdirichlet : ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ x, |harmonic n x - fkIsingSquareSampledImaginaryPart embedding Phi n x| < eta) :
-- imply
  ∀ eta : Real, 0 < eta → ∀ᶠ n in atTop, ∀ (p : FKIsingSquareRadialPatchPrimalNode (m n)), |base n + fkIsingSquareRadialPatchPrimitive n (m n) (lt_of_lt_of_le (Nat.zero_lt_of_lt p.1.1.2) (hm n)) (hm n) (Nat.zero_lt_of_lt p.1.1.2) p.1.1.1 p.1.2.1 - fkIsingSquareSampledImaginaryPart embedding Phi n (fkIsingSquareRadialPatchPrimalNodeVertex n (m n) (hm n) p)| < eta := by
-- proof
  apply StatMech.Universality.fkIsingSquareGrowingRadialPrimalPrimitive_uniform_convergence_to_imPhi embedding Phi upper lower harmonic eps m base hm hmpos hupper hlower hharmonic hupperBoundary hlowerBoundary hsandwich heps hdirichlet

/--
[fkIsingSquareRadialPatchPrimitive_laplacian_nonneg_of_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_laplacian_nonneg_of_even_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 ≤ m)
  (hj0 : 0 < j)
  (hj1 : j + 1 ≤ m)
  (heven : Even (i + j)) :
-- imply
  0 ≤ fkIsingSquareRadialPatchLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_laplacian_nonneg_of_even n m hn hm hmpos i j hi0 hi1 hj0 hj1 heven

/--
[fkIsingSquareRadialPatchPrimitive_laplacian_nonpos_of_odd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalRadialPatch.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPrimitive_laplacian_nonpos_of_odd_eq
  {n m : Nat}
  {i j : Nat}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hmpos : 0 < m)
  (hi0 : 0 < i)
  (hi1 : i + 1 ≤ m)
  (hj0 : 0 < j)
  (hj1 : j + 1 ≤ m)
  (hodd : ¬ Even (i + j)) :
-- imply
  fkIsingSquareRadialPatchLaplacian (fkIsingSquareRadialPatchPrimitive n m hn hm hmpos) i j ≤ 0 := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPrimitive_laplacian_nonpos_of_odd n m hn hm hmpos i j hi0 hi1 hj0 hj1 hodd


-- created on 2026-10-23
