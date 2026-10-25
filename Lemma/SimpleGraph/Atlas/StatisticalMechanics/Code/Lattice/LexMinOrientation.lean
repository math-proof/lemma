import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Lattice.LexMinOrientation.Part3
open Set SimpleGraph Function StatMech StatMech.Lattice


/--
[lmo_lexMinCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_lexMinCell_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ z₀ ∈ K, (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K ∧ (![z₀ 0, z₀ 1 - 1] : Site 2) ∉ K ∧ (∀ w ∈ K, z₀ 0 ≤ w 0) := by
-- proof
  apply StatMech.Lattice.lmo_lexMinCell K hK hne

/--
[lmo_leftDartAt_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_leftDartAt_dir_eq
  {z₀ : Site 2} :
-- imply
  (lmo_leftDartAt z₀).dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.lmo_leftDartAt_dir z₀

/--
[lmo_leftDartAt_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_leftDartAt_tail_eq
  {z₀ : Site 2} :
-- imply
  (lmo_leftDartAt z₀).tail = z₀ := by
-- proof
  apply StatMech.Lattice.lmo_leftDartAt_tail z₀

/--
[lmo_leftDartAt_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_leftDartAt_head_eq
  {z₀ : Site 2} :
-- imply
  (lmo_leftDartAt z₀).head = ![z₀ 0 - 1, z₀ 1] := by
-- proof
  apply StatMech.Lattice.lmo_leftDartAt_head z₀

/--
[lmo_leftDartAt_isBoundaryDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_leftDartAt_isBoundaryDart_eq
  {K : Set (Site 2)}
  {z₀ : Site 2}
-- given
  (hz₀ : z₀ ∈ K)
  (hwest : (![z₀ 0 - 1, z₀ 1] : Site 2) ∉ K) :
-- imply
  IsBoundaryDart K (lmo_leftDartAt z₀) := by
-- proof
  apply StatMech.Lattice.lmo_leftDartAt_isBoundaryDart hz₀ hwest

/--
[lmo_leftDartAt_face](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_leftDartAt_face_eq
  {z₀ : Site 2} :
-- imply
  dartFace (lmo_leftDartAt z₀) = ![z₀ 0 - 1, z₀ 1 - 1] := by
-- proof
  apply StatMech.Lattice.lmo_leftDartAt_face z₀

/--
[lmo_vertStep_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_vertStep_dir_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hv : (dartFace e) 0 = (dartFace (dartNext K e)) 0) :
-- imply
  e.dir = ![1, 0] ∨ e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.lmo_vertStep_dir e hv

/--
[lmo_vertStep_left_of_minCol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_vertStep_left_of_minCol_eq
  {K : Set (Site 2)}
  {m : ℤ}
  {e : Dart}
-- given
  (hm : ∀ w ∈ K, m ≤ w 0)
  (he : IsBoundaryDart K e)
  (hvert : (dartFace e) 0 = (dartFace (dartNext K e)) 0)
  (hcol : (dartFace e) 0 ≤ m - 1) :
-- imply
  e.dir = ![-1, 0] := by
-- proof
  apply StatMech.Lattice.lmo_vertStep_left_of_minCol m hm he hvert hcol

/--
[lmo_minVertStepLeft_of_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_minVertStepLeft_of_reachesLeftmost_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {m : ℤ}
-- given
  (hm : ∀ w ∈ K, m ≤ w 0)
  (hreach : lmo_OrbitReachesLeftmost K a m) :
-- imply
  shw_MinVertStepLeft K a := by
-- proof
  apply StatMech.Lattice.lmo_minVertStepLeft_of_reachesLeftmost K a m hm hreach

/--
[lmo_windingWitness_of_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_windingWitness_of_reachesLeftmost_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {m : ℤ}
-- given
  (hm : ∀ w ∈ K, m ≤ w 0)
  (hcyc : (mpl_orbitLoop K a).IsCycle)
  (hreach : lmo_OrbitReachesLeftmost K a m) :
-- imply
  wei_WindingWitness K a := by
-- proof
  apply StatMech.Lattice.lmo_windingWitness_of_reachesLeftmost K a m hm hcyc hreach

/--
[lmo_unitCell_minColumn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_unitCell_minColumn_eq :
-- imply
  ∀ w ∈ unitCell, (0 : ℤ) ≤ w 0 := by
-- proof
  apply StatMech.Lattice.lmo_unitCell_minColumn

/--
[lmo_unitCell_reachesLeftmost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_unitCell_reachesLeftmost_eq :
-- imply
  lmo_OrbitReachesLeftmost unitCell ucBase 0 := by
-- proof
  apply StatMech.Lattice.lmo_unitCell_reachesLeftmost

/--
[lmo_unitCell_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_unitCell_windingWitness_eq :
-- imply
  wei_WindingWitness unitCell ucBase := by
-- proof
  apply StatMech.Lattice.lmo_unitCell_windingWitness

/--
[lmo_face_col_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_face_col_left_eq
  {e : Dart}
-- given
  (hd : e.dir = ![-1, 0]) :
-- imply
  (dartFace e) 0 = e.tail 0 - 1 := by
-- proof
  apply StatMech.Lattice.lmo_face_col_left hd

/--
[lmo_face_col_up](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_face_col_up_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, 1]) :
-- imply
  (dartFace e) 0 = e.tail 0 - 1 := by
-- proof
  apply StatMech.Lattice.lmo_face_col_up hd

/--
[lmo_face_col_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_face_col_right_eq
  {e : Dart}
-- given
  (hd : e.dir = ![1, 0]) :
-- imply
  (dartFace e) 0 = e.tail 0 := by
-- proof
  apply StatMech.Lattice.lmo_face_col_right hd

/--
[lmo_face_col_down](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_face_col_down_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  (dartFace e) 0 = e.tail 0 := by
-- proof
  apply StatMech.Lattice.lmo_face_col_down hd

/--
[lmo_reachesLeftmost_of_left_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/LexMinOrientation.lean)
-/
@[path]
private lemma lmo_reachesLeftmost_of_left_tail_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {m : ℤ}
  {k : ℕ}
-- given
  (hk : k < dartOrbitPeriod K a)
  (htail : ((dartNext K)^[k] a.1).tail 0 = m)
  (hd : ((dartNext K)^[k] a.1).dir = ![-1, 0]) :
-- imply
  lmo_OrbitReachesLeftmost K a m := by
-- proof
  apply StatMech.Lattice.lmo_reachesLeftmost_of_left_tail K a m hk htail hd


-- created on 2026-10-23
