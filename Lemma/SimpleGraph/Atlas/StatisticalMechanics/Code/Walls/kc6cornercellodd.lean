import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.kc6cornercellodd
open Set SimpleGraph Function StatMech StatMech.Walls


/--
[kc6_topWallCount_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_topWallCount_eq_one_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc10core_topWallCount c (mpl_orbitLoop K (extremeBase K c hc)) = 1 := by
-- proof
  apply StatMech.Walls.kc6_topWallCount_eq_one K hK c hc

/--
[kc6_topWallOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_topWallOdd_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  jc10core_TopWallOdd K (extremeBase K c hc) c := by
-- proof
  apply StatMech.Walls.kc6_topWallOdd K hK c hc

/--
[kc6_cornerCellOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_cornerCellOdd_eq
  {K : Set (Site 2)}
  {c : Site 2}
-- given
  (hK : K.Finite)
  (hc : IsExtremeCell K c) :
-- imply
  ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.kc6_cornerCellOdd K hK c hc

/--
[kc6_cornerCellOdd_of_topWallOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_cornerCellOdd_of_topWallOdd_eq
  {K : Set (Site 2)}
  {a : {e : Dart // IsBoundaryDart K e}}
  {c : Site 2}
-- given
  (hc : IsExtremeCell K c)
  (htop : jc10core_TopWallOdd K a c) :
-- imply
  ¬ Even (jec_rayCount c (mpl_orbitLoop K a)) := by
-- proof
  apply StatMech.Walls.kc6_cornerCellOdd_of_topWallOdd K a c hc htop

/--
[kc6_exists_windingWitness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_exists_windingWitness_eq
  {K : Set (Site 2)}
-- given
  (hK : K.Finite)
  (hne : K.Nonempty) :
-- imply
  ∃ c : Site 2, ∃ hc : IsExtremeCell K c, c ∈ K ∧ ¬ Even (jec_rayCount c (mpl_orbitLoop K (extremeBase K c hc))) := by
-- proof
  apply StatMech.Walls.kc6_exists_windingWitness K hK hne

/--
[kc6_unitCell_isExtremeCell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_unitCell_isExtremeCell_eq :
-- imply
  IsExtremeCell unitCell (![0, 0] : Site 2) where mem := by
-- proof
  apply StatMech.Walls.kc6_unitCell_isExtremeCell

/--
[kc6_unitCell_cornerCellOdd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kc6cornercellodd.lean)
-/
@[path]
private lemma kc6_unitCell_cornerCellOdd_eq :
-- imply
  ¬ Even (jec_rayCount (![0, 0] : Site 2) (mpl_orbitLoop unitCell (extremeBase unitCell (![0, 0] : Site 2) kc6_unitCell_isExtremeCell))) := by
-- proof
  apply StatMech.Walls.kc6_unitCell_cornerCellOdd


-- created on 2026-10-23
