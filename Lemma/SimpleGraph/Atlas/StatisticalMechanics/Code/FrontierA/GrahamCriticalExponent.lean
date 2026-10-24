import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.GrahamCriticalExponent
open Filter Set StatMech StatMech.FrontierA


/--
[grahamCriticalExponent_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCriticalExponent.lean)
-/
@[path]
private lemma grahamCriticalExponent_inequality_eq
  {beta gamma delta3 : Real}
-- given
  (M chi D : Real -> Real)
  (hMpos : forall t, 0 < t -> t < 1 -> 0 < M t)
  (hchipos : forall t, 0 < t -> t < 1 -> 0 < chi t)
  (hDpos : forall t, 0 < t -> t < 1 -> 0 < D t)
  (hineq : forall t, 0 < t -> t < 1 -> 2 * chi t ^ 2 * M t <= D t)
  (hM : HasGrahamCriticalExponent M beta)
  (hchi : HasGrahamCriticalExponent chi (-gamma))
  (hD : HasGrahamCriticalExponent D (-(gamma + delta3))) :
-- imply
  gamma - beta <= delta3 := by
-- proof
  apply StatMech.FrontierA.grahamCriticalExponent_inequality M chi D beta gamma delta3 hMpos hchipos hDpos hineq hM hchi hD


-- created on 2026-10-23
