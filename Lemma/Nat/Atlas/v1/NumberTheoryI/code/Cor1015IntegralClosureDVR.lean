import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.Cor1015IntegralClosureDVR
open IsLocalRing


/--
[integralClosure_isDVR](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1015IntegralClosureDVR.lean)
-/
@[path]
lemma integralClosure_isDVR
  {A : Type*}
  [CommRing A]
  [IsDomain A]
  [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  {K : Type*}
  [Field K]
  [Algebra A K]
  [IsFractionRing A K]
  {E : Type*}
  [Field E]
  [Algebra K E]
  [FiniteDimensional K E]
  [Algebra.IsSeparable K E]
  [Algebra A E]
  [IsScalarTower A K E] :
-- imply
  IsDiscreteValuationRing (integralClosure A E) :=
-- proof
  integral_closure_complete_DVR_is_DVR A K E (integralClosure A E)


-- created on 2026-10-23
