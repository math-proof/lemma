import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc2_downfaceoutK
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_dartFace_down_eq_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_downfaceoutK.lean)
-/
@[path]
private lemma kc2_dartFace_down_eq_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace e = e.head := by
-- proof
  apply StatMech.Walls.kc2_dartFace_down_eq_head e hd

/--
[kc2_dartFace_down_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_downfaceoutK.lean)
-/
@[path]
private lemma kc2_dartFace_down_notMem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace e ∉ K := by
-- proof
  apply StatMech.Walls.kc2_dartFace_down_notMem he hd

/--
[kc2_down_face_even_of_supportOddInK](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_downfaceoutK.lean)
-/
@[path]
private lemma kc2_down_face_even_of_supportOddInK_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1])
  (hsupp : dartFace e ∈ (mpl_orbitLoop K a).support)
  (hres : exc_SupportOddInK K a) :
-- imply
  Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc2_down_face_even_of_supportOddInK K a he hd hsupp hres


-- created on 2026-10-23
