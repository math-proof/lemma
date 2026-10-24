import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheRapidityTrigonometry
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexRapidityCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexRapidityCircle_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  HasDerivAt (sixVertexRapidityCircle lam) (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I * sixVertexRapidityCircle lam alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexRapidityCircle hlam alpha

/--
[hasDerivAt_sixVertexMomentumCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexMomentumCircle_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  HasDerivAt (sixVertexMomentumCircle lam) (((sixVertexXiFourier lam alpha : Real) : Complex) * Complex.I * sixVertexMomentumCircle lam alpha) alpha := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexMomentumCircle hlam alpha

/--
[sixVertexRapidityCircle_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma sixVertexRapidityCircle_ne_zero_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexRapidityCircle lam alpha ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexRapidityCircle_ne_zero hlam alpha

/--
[sixVertexMomentumCircle_eq_rapidityCircle](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma sixVertexMomentumCircle_eq_rapidityCircle_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  sixVertexMomentumCircle lam alpha = sixVertexRapidityCircle lam alpha := by
-- proof
  apply StatMech.FrontierD.sixVertexMomentumCircle_eq_rapidityCircle hlam alpha

/--
[cos_sixVertexRapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma cos_sixVertexRapidityMomentum_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Real.cos (sixVertexRapidityMomentum lam alpha) = (Real.cosh lam * Real.cos alpha - 1) / (Real.cosh lam - Real.cos alpha) := by
-- proof
  apply StatMech.FrontierD.cos_sixVertexRapidityMomentum hlam alpha

/--
[sin_sixVertexRapidityMomentum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRapidityTrigonometry.lean)
-/
@[path]
private lemma sin_sixVertexRapidityMomentum_eq
  {lam : Real}
  {alpha : Real}
-- given
  (hlam : 0 < lam) :
-- imply
  Real.sin (sixVertexRapidityMomentum lam alpha) = Real.sinh lam * Real.sin alpha / (Real.cosh lam - Real.cos alpha) := by
-- proof
  apply StatMech.FrontierD.sin_sixVertexRapidityMomentum hlam alpha


-- created on 2026-10-23
