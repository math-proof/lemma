import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.FKQgt4ParameterBridge
open StatMech StatMech.FrontierD


/--
[fkQgt4SixVertexWeight_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4ParameterBridge.lean)
-/
@[path]
private lemma fkQgt4SixVertexWeight_sq_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  fkQgt4SixVertexWeight q ^ 2 = 2 + Real.sqrt q := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexWeight_sq hq

/--
[two_lt_fkQgt4SixVertexWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4ParameterBridge.lean)
-/
@[path]
private lemma two_lt_fkQgt4SixVertexWeight_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  2 < fkQgt4SixVertexWeight q := by
-- proof
  apply StatMech.FrontierD.two_lt_fkQgt4SixVertexWeight hq

/--
[cosh_sixVertexAntiferroelectricLambda_fkQgt4](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4ParameterBridge.lean)
-/
@[path]
private lemma cosh_sixVertexAntiferroelectricLambda_fkQgt4_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  Real.cosh (sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) = Real.sqrt q / 2 := by
-- proof
  apply StatMech.FrontierD.cosh_sixVertexAntiferroelectricLambda_fkQgt4 hq

/--
[sixVertexAntiferroelectricLambda_fkQgt4_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4ParameterBridge.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_fkQgt4_pos_eq
  {q : ℝ}
-- given
  (hq : 4 < q) :
-- imply
  0 < sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_fkQgt4_pos hq


-- created on 2026-10-23
