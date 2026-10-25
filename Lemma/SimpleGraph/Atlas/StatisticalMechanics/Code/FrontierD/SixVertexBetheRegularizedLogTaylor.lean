import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheRegularizedLogTaylor.Part4
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexRegularizedBetheLogNormDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexRegularizedBetheLogNormDerivative_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  HasDerivAt (sixVertexRegularizedBetheLogNormDerivative c epsilon) (sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexRegularizedBetheLogNormDerivative hc hepsilon

/--
[abs_sixVertexRegularizedBetheLogNormSecondDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma abs_sixVertexRegularizedBetheLogNormSecondDerivative_le_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  |sixVertexRegularizedBetheLogNormSecondDerivative c epsilon x| <= sixVertexRegularizedBetheLogNormSecondDerivativeBound c epsilon := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRegularizedBetheLogNormSecondDerivative_le hc hepsilon

/--
[lipschitzWith_sixVertexRegularizedBetheLogNormDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma lipschitzWith_sixVertexRegularizedBetheLogNormDerivative_eq
  {c epsilon : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  LipschitzWith (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon) (sixVertexRegularizedBetheLogNormDerivative c epsilon) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_sixVertexRegularizedBetheLogNormDerivative hc hepsilon

/--
[abs_sixVertexRegularizedBetheLogNormDerivative_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma abs_sixVertexRegularizedBetheLogNormDerivative_le_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  |sixVertexRegularizedBetheLogNormDerivative c epsilon x| <= sixVertexRegularizedBetheLogNormDerivativeBound c epsilon := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRegularizedBetheLogNormDerivative_le hc hepsilon

/--
[lipschitzWith_mul_div_sixVertexFiniteRootDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma lipschitzWith_mul_div_sixVertexFiniteRootDensity_eq
  {c : Real}
  {N n : Nat}
  {lower U G : Real}
  {u tau : Real -> Real}
  {Lu D : NNReal}
-- given
  (hc : 2 < c)
  (hN : 0 < N)
  (hn : n <= N)
  (p : Fin n -> Real)
  (hlower : 0 < lower)
  (hU : 0 <= U)
  (hG : 0 <= G)
  (hdensity : forall y, lower <= sixVertexFiniteRootDensity c N n p y)
  (huLip : LipschitzWith Lu u)
  (huBound : forall y, |u y| <= U)
  (htauLip : LipschitzWith D tau)
  (htauBound : forall y, |tau y| <= G) :
-- imply
  LipschitzWith (sixVertexLogOffsetQuotientLipschitzNNReal c lower U G Lu D) (fun y => u y * tau y / sixVertexFiniteRootDensity c N n p y) := by
-- proof
  apply StatMech.FrontierD.lipschitzWith_mul_div_sixVertexFiniteRootDensity hc hN hn p hlower hU hG hdensity huLip huBound htauLip htauBound

/--
[abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheRegularizedLogTaylor.lean)
-/
@[path]
private lemma abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le_eq
  {c epsilon : Real}
  {a b : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon) :
-- imply
  |sixVertexRegularizedBetheLogKernel c epsilon b - sixVertexRegularizedBetheLogKernel c epsilon a - sixVertexRegularizedBetheLogNormDerivative c epsilon a * (b - a)| <= (sixVertexRegularizedBetheLogNormSecondDerivativeNNReal c epsilon : Real) * |b - a| ^ 2 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexRegularizedBetheLogKernel_sub_linearization_le hc hepsilon a b


-- created on 2026-10-23
