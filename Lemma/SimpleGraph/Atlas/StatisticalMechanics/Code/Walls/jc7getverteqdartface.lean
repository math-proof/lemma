import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.jc7getverteqdartface
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[jc7_dartOrbitFaceWalk_getVert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_dartOrbitFaceWalk_getVert_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n k : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (hk : k ≤ n) :
-- imply
  (dartOrbitFaceWalk K e he n).getVert k = dartFace ((dartNext K)^[k] e) := by
-- proof
  apply StatMech.Walls.jc7_dartOrbitFaceWalk_getVert K e he n k hk

/--
[jc7_dartOrbitFaceLoop_getVert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_dartOrbitFaceLoop_getVert_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hn : n ≤ (dartNext_periodic K hK e he).choose) :
-- imply
  (dartOrbitFaceLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Walls.jc7_dartOrbitFaceLoop_getVert K hK e he n hn

/--
[jc7_orbitLoop_length_eq_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_orbitLoop_length_eq_period_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (olb_orbitLoop K hK e he).length = (dartNext_periodic K hK e he).choose := by
-- proof
  apply StatMech.Walls.jc7_orbitLoop_length_eq_period K hK e he

/--
[jc7_orbitLoop_getVert_eq_dartFace_period](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_orbitLoop_getVert_eq_dartFace_period_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hn : n ≤ (dartNext_periodic K hK e he).choose) :
-- imply
  (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Walls.jc7_orbitLoop_getVert_eq_dartFace_period K hK e he n hn

/--
[jc7_getVert_eq_dartFace](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_getVert_eq_dartFace_eq
  {K : Set (Site 2)}
  {e : Dart}
  {n : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hn : n ≤ (olb_orbitLoop K hK e he).length) :
-- imply
  (olb_orbitLoop K hK e he).getVert n = dartFace ((dartNext K)^[n] e) := by
-- proof
  apply StatMech.Walls.jc7_getVert_eq_dartFace K hK e he n hn

/--
[jc7_orbitLoop_getVert_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc7getverteqdartface.lean)
-/
@[path]
private lemma jc7_orbitLoop_getVert_zero_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e) :
-- imply
  (olb_orbitLoop K hK e he).getVert 0 = dartFace e := by
-- proof
  apply StatMech.Walls.jc7_orbitLoop_getVert_zero K hK e he


-- created on 2026-10-23
