import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBethePhysicalCoordinate
open StatMech StatMech.FrontierD


/--
[sixVertexAnisotropyMagnitude_eq_cosh_lambda](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalCoordinate.lean)
-/
@[path]
private lemma sixVertexAnisotropyMagnitude_eq_cosh_lambda_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexAnisotropyMagnitude c = Real.cosh (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexAnisotropyMagnitude_eq_cosh_lambda hc

/--
[sixVertexRootDensityScale_eq_sinh_lambda](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalCoordinate.lean)
-/
@[path]
private lemma sixVertexRootDensityScale_eq_sinh_lambda_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityScale c = Real.sinh (sixVertexAntiferroelectricLambda c) := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityScale_eq_sinh_lambda hc

/--
[sixVertexRootDensityWeight_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalCoordinate.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_rapidityMomentum_eq
  {c : Real}
  {alpha : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityWeight c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) = sixVertexXiFourier (sixVertexAntiferroelectricLambda c) alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_rapidityMomentum hc alpha

/--
[sixVertexRootDensityKernel_rapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBethePhysicalCoordinate.lean)
-/
@[path]
private lemma sixVertexRootDensityKernel_rapidityMomentum_eq
  {c : Real}
  {alpha beta : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexRootDensityKernel c (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) alpha) (sixVertexRapidityMomentum (sixVertexAntiferroelectricLambda c) beta) = sixVertexXiFourier (2 * sixVertexAntiferroelectricLambda c) (alpha - beta) := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityKernel_rapidityMomentum hc alpha beta


-- created on 2026-10-23
