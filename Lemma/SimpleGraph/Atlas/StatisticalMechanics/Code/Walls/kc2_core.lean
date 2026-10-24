import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.kc2_core
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc2_supportOdd_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOdd_right_eq
  {K : Set (Site 2)}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![1, 0]) :
-- imply
  dartFace e ∈ K := by
-- proof
  apply StatMech.Walls.kc2_supportOdd_right he hd

/--
[kc2_supportOddNonRight_of_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOddNonRight_of_core_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : exc_SupportOddInK K a) :
-- imply
  kc2_SupportOddNonRight K a := by
-- proof
  apply StatMech.Walls.kc2_supportOddNonRight_of_core h

/--
[kc2_supportOddInK_of_nonRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOddInK_of_nonRight_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (h : kc2_SupportOddNonRight K a) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc2_supportOddInK_of_nonRight h

/--
[kc2_supportOddInK_iff_nonRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOddInK_iff_nonRight_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  exc_SupportOddInK K a ↔ kc2_SupportOddNonRight K a := by
-- proof
  apply StatMech.Walls.kc2_supportOddInK_iff_nonRight

/--
[kc2_down_residue_is_evenRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_down_residue_is_evenRay_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {e : Dart}
-- given
  (he : IsBoundaryDart K e)
  (hd : e.dir = ![0, -1]) :
-- imply
  (¬ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) → dartFace e ∈ K) ↔ Even (jec_rayCount (dartFace e) (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc2_down_residue_is_evenRay he hd

/--
[kc2_supportOddNonRight_iff_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOddNonRight_iff_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  kc2_SupportOddNonRight K a ↔ kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a := by
-- proof
  apply StatMech.Walls.kc2_supportOddNonRight_iff_three

/--
[kc2_supportOddInK_of_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_supportOddInK_of_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
-- given
  (hdown : kc2_DownFaceEven K a)
  (hup : kc2_UpFaceInK K a)
  (hleft : kc2_LeftFaceInK K a) :
-- imply
  exc_SupportOddInK K a := by
-- proof
  apply StatMech.Walls.kc2_supportOddInK_of_three hdown hup hleft

/--
[kc2_unitCell_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_unitCell_core_eq :
-- imply
  exc_SupportOddInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc2_unitCell_core

/--
[kc2_unitCell_supportOddNonRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_unitCell_supportOddNonRight_eq :
-- imply
  kc2_SupportOddNonRight unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc2_unitCell_supportOddNonRight

/--
[kc2_unitCell_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_unitCell_three_eq :
-- imply
  kc2_DownFaceEven unitCell ucBase ∧ kc2_UpFaceInK unitCell ucBase ∧ kc2_LeftFaceInK unitCell ucBase := by
-- proof
  apply StatMech.Walls.kc2_unitCell_three

/--
[kc2_core_iff_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc2_core.lean)
-/
@[path]
private lemma kc2_core_iff_three_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}} :
-- imply
  exc_SupportOddInK K a ↔ (kc2_DownFaceEven K a ∧ kc2_UpFaceInK K a ∧ kc2_LeftFaceInK K a) := by
-- proof
  apply StatMech.Walls.kc2_core_iff_three


-- created on 2026-10-23
