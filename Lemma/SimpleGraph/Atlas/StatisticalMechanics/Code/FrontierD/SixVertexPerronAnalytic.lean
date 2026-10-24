import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexPerronAnalytic
open Finset Matrix Filter Topology StatMech StatMech.FrontierD


/--
[analyticAt_sixVertexSectorTransfer_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexSectorTransfer_apply_eq
  {N n : Nat}
  {x y : SixVertexSector N n}
  {c : Real} :
-- imply
  AnalyticAt Real (fun t ↦ sixVertexSectorTransfer N n t x y) c := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexSectorTransfer_apply N n x y c

/--
[analyticAt_sixVertexSectorCharacteristicDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexSectorCharacteristicDet_eq
  {N n : Nat}
  {z : Real × Real} :
-- imply
  AnalyticAt Real (fun q : Real × Real ↦ Matrix.det (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n q.1)) z := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexSectorCharacteristicDet N n z

/--
[analyticOnNhd_sixVertexSectorCharacteristicDet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexSectorCharacteristicDet_eq
  {N n : Nat} :
-- imply
  AnalyticOnNhd Real (fun q : Real × Real ↦ Matrix.det (q.2 • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n q.1)) Set.univ := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexSectorCharacteristicDet N n

/--
[sixVertexSectorTop_charpoly_rootMultiplicity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma sixVertexSectorTop_charpoly_rootMultiplicity_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  (sixVertexSectorTransfer N n c).charpoly.rootMultiplicity (sixVertexSectorTopEigenvalue N n hn c) = 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_charpoly_rootMultiplicity hn hc

/--
[sixVertexSectorTop_charpoly_derivative_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma sixVertexSectorTop_charpoly_derivative_ne_zero_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  (sixVertexSectorTransfer N n c).charpoly.derivative.eval (sixVertexSectorTopEigenvalue N n hn c) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTop_charpoly_derivative_ne_zero hn hc

/--
[sixVertexSectorTopEigenvalue_eq_sSup](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma sixVertexSectorTopEigenvalue_eq_sSup_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N) :
-- imply
  sixVertexSectorTopEigenvalue N n hn c = sSup ((fun x : EuclideanSpace Real (SixVertexSector N n) ↦ (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap |>.reApplyInnerSelf x) '' Metric.sphere 0 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTopEigenvalue_eq_sSup hn c

/--
[continuous_sixVertexSectorRayleighFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexSectorRayleighFamily_eq
  {N n : Nat} :
-- imply
  Continuous (Function.uncurry fun c : Real ↦ fun x : EuclideanSpace Real (SixVertexSector N n) ↦ (Matrix.toEuclideanLin (sixVertexSectorTransfer N n c)).toContinuousLinearMap.reApplyInnerSelf x) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSectorRayleighFamily N n

/--
[continuous_sixVertexSectorTopEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma continuous_sixVertexSectorTopEigenvalue_eq
  {N n : Nat}
-- given
  (hn : n ≤ N) :
-- imply
  Continuous (sixVertexSectorTopEigenvalue N n hn) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSectorTopEigenvalue hn

/--
[sixVertexSectorCharacteristicDet_top_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma sixVertexSectorCharacteristicDet_top_eq_zero_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N) :
-- imply
  Matrix.det (sixVertexSectorTopEigenvalue N n hn c • (1 : Matrix (SixVertexSector N n) (SixVertexSector N n) Real) - sixVertexSectorTransfer N n c) = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorCharacteristicDet_top_eq_zero hn c

/--
[analyticAt_sixVertexSectorTopEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma analyticAt_sixVertexSectorTopEigenvalue_eq
  {N n : Nat}
  {c : Real}
-- given
  (hn : n ≤ N)
  (hc : 0 < c) :
-- imply
  AnalyticAt Real (sixVertexSectorTopEigenvalue N n hn) c := by
-- proof
  apply StatMech.FrontierD.analyticAt_sixVertexSectorTopEigenvalue hn hc

/--
[analyticOnNhd_sixVertexSectorTopEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexPerronAnalytic.lean)
-/
@[path]
private lemma analyticOnNhd_sixVertexSectorTopEigenvalue_eq
  {N n : Nat}
-- given
  (hn : n ≤ N) :
-- imply
  AnalyticOnNhd Real (sixVertexSectorTopEigenvalue N n hn) (Set.Ioi 0) := by
-- proof
  apply StatMech.FrontierD.analyticOnNhd_sixVertexSectorTopEigenvalue hn


-- created on 2026-10-23
