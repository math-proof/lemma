import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionRectangularModel.Part4
open StatMech StatMech.FrontierA


/--
[rectangularDobrushinFreeEnergy_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_nonneg_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 <= rectangularDobrushinFreeEnergy beta m n := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinFreeEnergy_nonneg hbeta m n

/--
[rectangularDobrushinFreeEnergy_eq_dualIsingDisorder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_eq_dualIsingDisorder_eq
  {beta : Real}
  {m n : Nat}
-- given
  (hbeta : 0 < beta)
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  rectangularDobrushinFreeEnergy beta m n = cubicalRectangularDisorderFreeEnergy beta m n := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinFreeEnergy_eq_dualIsingDisorder hbeta hm hn

/--
[rectangularDobrushinFreeEnergy_areaBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_areaBound_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  HasRectangularAreaBound (rectangularDobrushinFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinFreeEnergy_areaBound hbeta

/--
[rectangularDobrushinFreeEnergy_separatelySubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushinFreeEnergy_separatelySubadditive_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  SeparatelySubadditive (rectangularDobrushinFreeEnergy beta) := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinFreeEnergy_separatelySubadditive hbeta

/--
[rectangularDobrushinSurfaceRate_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushinSurfaceRate_nonneg_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  0 <= rectangularDobrushinSurfaceRate beta := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushinSurfaceRate_nonneg hbeta

/--
[rectangularDobrushin_square_and_iterated_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularDobrushin_square_and_iterated_tendsto_eq
  {beta : Real}
-- given
  (hbeta : 0 < beta) :
-- imply
  Filter.Tendsto (fun n : Nat => rectangularSurfaceDensity (rectangularDobrushinFreeEnergy beta) n n) Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) /\ Filter.Tendsto (fun k : Nat => ((rectangularDobrushinFreeEnergy_separatelySubadditive hbeta).1 k).lim / (k : Real)) Filter.atTop (nhds (rectangularDobrushinSurfaceRate beta)) := by
-- proof
  apply StatMech.FrontierA.rectangularDobrushin_square_and_iterated_tendsto hbeta

/--
[rectangularIsingDobrushinFreeEnergy_eq_disorder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularIsingDobrushinFreeEnergy_eq_disorder_eq
  {J : Real}
  {m n : Nat}
-- given
  (hJ : 0 < J)
  (hm : 0 < m)
  (hn : 0 < n) :
-- imply
  rectangularIsingDobrushinFreeEnergy J m n = finiteRectangularIsingDisorderFreeEnergy J m n := by
-- proof
  apply StatMech.FrontierA.rectangularIsingDobrushinFreeEnergy_eq_disorder hJ hm hn

/--
[rectangularIsingDobrushinFreeEnergy_separatelySubadditive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularIsingDobrushinFreeEnergy_separatelySubadditive_eq
  {J : Real}
-- given
  (hJ : 0 < J) :
-- imply
  SeparatelySubadditive (rectangularIsingDobrushinFreeEnergy J) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ

/--
[rectangularIsingDobrushinFreeEnergy_areaBound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularIsingDobrushinFreeEnergy_areaBound_eq
  {J : Real}
-- given
  (hJ : 0 < J) :
-- imply
  HasRectangularAreaBound (rectangularIsingDobrushinFreeEnergy J) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingDobrushinFreeEnergy_areaBound hJ

/--
[rectangularIsingSurfaceTension_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularIsingSurfaceTension_nonneg_eq
  {J : Real}
-- given
  (hJ : 0 < J) :
-- imply
  0 <= rectangularIsingSurfaceTension J := by
-- proof
  apply StatMech.FrontierA.rectangularIsingSurfaceTension_nonneg hJ

/--
[rectangularIsingDobrushin_square_and_iterated_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionRectangularModel.lean)
-/
@[path]
private lemma rectangularIsingDobrushin_square_and_iterated_tendsto_eq
  {J : Real}
-- given
  (hJ : 0 < J) :
-- imply
  Filter.Tendsto (fun n : Nat => rectangularSurfaceDensity (rectangularIsingDobrushinFreeEnergy J) n n) Filter.atTop (nhds (rectangularIsingSurfaceTension J)) /\ Filter.Tendsto (fun k : Nat => ((rectangularIsingDobrushinFreeEnergy_separatelySubadditive hJ).1 k).lim / (k : Real)) Filter.atTop (nhds (rectangularIsingSurfaceTension J)) := by
-- proof
  apply StatMech.FrontierA.rectangularIsingDobrushin_square_and_iterated_tendsto hJ


-- created on 2026-10-23
