import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc_orbitloopedges
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc_orbitFaceLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_orbitloopedges.lean)
-/
@[path]
private lemma kc_orbitFaceLoop_edges_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitFaceLoop K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
-- proof
  apply StatMech.Walls.kc_orbitFaceLoop_edges K a

/--
[kc_orbitLoop_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_orbitloopedges.lean)
-/
@[path]
private lemma kc_orbitLoop_edges_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  (mpl_orbitLoop K a).edges = (List.range (dartOrbitPeriod K a)).map (fun k => s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1))) := by
-- proof
  apply StatMech.Walls.kc_orbitLoop_edges K a

/--
[kc_orbitLoop_rayCount_eq_countP](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_orbitloopedges.lean)
-/
@[path]
private lemma kc_orbitLoop_rayCount_eq_countP_eq
  {z : Site 2}
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = (List.range (dartOrbitPeriod K a)).countP (fun k => decide (jec_rayEdge z s(dartFace ((dartNext K)^[k] a.1), dartFace ((dartNext K)^[k + 1] a.1)))) := by
-- proof
  apply StatMech.Walls.kc_orbitLoop_rayCount_eq_countP z K a

/--
[kc_rayCount_congr_of_face_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc_orbitloopedges.lean)
-/
@[path]
private lemma kc_rayCount_congr_of_face_eq_eq
  {z : Site 2}
  {K K' : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {a' : {e : Dart // IsBoundaryDart K' e}}
-- given
  (hper : dartOrbitPeriod K a = dartOrbitPeriod K' a')
  (hface : ∀ k ≤ dartOrbitPeriod K a, dartFace ((dartNext K)^[k] a.1) = dartFace ((dartNext K')^[k] a'.1)) :
-- imply
  jec_rayCount z (mpl_orbitLoop K a) = jec_rayCount z (mpl_orbitLoop K' a') := by
-- proof
  apply StatMech.Walls.kc_rayCount_congr_of_face_eq z a a' hper hface


-- created on 2026-10-23
