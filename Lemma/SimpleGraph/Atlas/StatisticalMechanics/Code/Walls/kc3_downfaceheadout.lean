import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc3_downfaceheadout
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc3_dartFace_down_eq_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_dartFace_down_eq_head_eq
  {e : Dart}
-- given
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace e = e.head := by
-- proof
  apply StatMech.Walls.kc3_dartFace_down_eq_head e hd

/--
[kc3_down_head_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_down_head_notMem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (_hd : e.dir = ![0, -1]) :
-- imply
  e.head ∉ K := by
-- proof
  apply StatMech.Walls.kc3_down_head_notMem he _hd

/--
[kc3_dartFace_down_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_dartFace_down_notMem_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1]) :
-- imply
  dartFace e ∉ K := by
-- proof
  apply StatMech.Walls.kc3_dartFace_down_notMem he hd

/--
[kc3_down_zInK_unattainable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_down_zInK_unattainable_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1]) :
-- imply
  ¬ (dartFace e ∈ K) := by
-- proof
  apply StatMech.Walls.kc3_down_zInK_unattainable he hd

/--
[kc3_down_zInK_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_down_zInK_false_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1])
  (hmem : dartFace e ∈ K) :
-- imply
  False := by
-- proof
  apply StatMech.Walls.kc3_down_zInK_false he hd hmem

/--
[kc3_down_supportOdd_forces_even](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_down_supportOdd_forces_even_eq
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
  apply StatMech.Walls.kc3_down_supportOdd_forces_even K a he hd hsupp hres

/--
[kc3_downDart_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_downDart_dir_eq :
-- imply
  kc3_downDart.dir = ![0, -1] := by
-- proof
  apply StatMech.Walls.kc3_downDart_dir

/--
[kc3_downDart_isBoundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_downDart_isBoundary_eq :
-- imply
  IsBoundaryDart kc3_upperHalf kc3_downDart := by
-- proof
  apply StatMech.Walls.kc3_downDart_isBoundary

/--
[kc3_downDart_face_notMem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc3_downfaceheadout.lean)
-/
@[path]
private lemma kc3_downDart_face_notMem_eq :
-- imply
  dartFace kc3_downDart ∉ kc3_upperHalf := by
-- proof
  apply StatMech.Walls.kc3_downDart_face_notMem


-- created on 2026-10-23
