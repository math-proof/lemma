import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4NearFourParameterAsymptotic
open Filter Topology Asymptotics StatMech StatMech.FrontierD


/--
[sinh_sub_id_isLittleO_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma sinh_sub_id_isLittleO_sq_eq :
-- imply
  (fun x : Real => Real.sinh x - x) =o[nhds 0] (fun x : Real => x ^ 2) := by
-- proof
  apply StatMech.FrontierD.sinh_sub_id_isLittleO_sq

/--
[one_div_sub_one_div_sinh_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma one_div_sub_one_div_sinh_tendsto_zero_eq :
-- imply
  Tendsto (fun x : Real => 1 / x - 1 / Real.sinh x) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
-- proof
  apply StatMech.FrontierD.one_div_sub_one_div_sinh_tendsto_zero

/--
[exp_gap_lambda_div_exp_gap_sinh_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma exp_gap_lambda_div_exp_gap_sinh_tendsto_one_eq :
-- imply
  Tendsto (fun lam : Real => Real.exp (-(Real.pi ^ 2) / (2 * lam)) / Real.exp (-(Real.pi ^ 2) / (2 * Real.sinh lam))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.exp_gap_lambda_div_exp_gap_sinh_tendsto_one

/--
[sixVertexAntiferroelectricLambda_fkQgt4_eq_arcosh](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_fkQgt4_eq_arcosh_eq
  {q : Real}
-- given
  (hq : 4 < q) :
-- imply
  sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) = Real.arcosh (Real.sqrt q / 2) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_fkQgt4_eq_arcosh hq

/--
[sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero_eq :
-- imply
  Tendsto (fun q : Real => sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q)) (nhdsWithin 4 (Set.Ioi 4)) (nhdsWithin 0 (Set.Ioi 0)) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricLambda_fkQgt4_tendsto_zero

/--
[fkQgt4_exp_lambda_div_exp_sqrt_sub_four_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma fkQgt4_exp_lambda_div_exp_sqrt_sub_four_tendsto_one_eq :
-- imply
  Tendsto (fun q : Real => let lam := sixVertexAntiferroelectricLambda (fkQgt4SixVertexWeight q) Real.exp (-(Real.pi ^ 2) / (2 * lam)) / Real.exp (-(Real.pi ^ 2) / Real.sqrt (q - 4))) (nhdsWithin 4 (Set.Ioi 4)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.fkQgt4_exp_lambda_div_exp_sqrt_sub_four_tendsto_one

/--
[sixVertexAntiferroelectricGapRate_div_exp_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma sixVertexAntiferroelectricGapRate_div_exp_tendsto_one_eq :
-- imply
  Tendsto (fun lam : Real => sixVertexAntiferroelectricGapRate lam / (8 * Real.exp (-(Real.pi ^ 2) / (2 * lam)))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexAntiferroelectricGapRate_div_exp_tendsto_one

/--
[fkQgt4SixVertexGapRate_div_exp_sqrt_sub_four_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4NearFourParameterAsymptotic.lean)
-/
@[path]
private lemma fkQgt4SixVertexGapRate_div_exp_sqrt_sub_four_tendsto_one_eq :
-- imply
  Tendsto (fun q : Real => fkQgt4SixVertexGapRate q / (8 * Real.exp (-(Real.pi ^ 2) / Real.sqrt (q - 4)))) (nhdsWithin 4 (Set.Ioi 4)) (nhds 1) := by
-- proof
  apply StatMech.FrontierD.fkQgt4SixVertexGapRate_div_exp_sqrt_sub_four_tendsto_one


-- created on 2026-10-23
