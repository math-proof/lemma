import Mathlib.Algebra.Module.LinearMap.Defs
import Instance.Mathlib_IsModuleTopology
import Def.IsModuleTopology
import Initialize.Tactic.Attr.Basic


@[path]
private lemma main
  [Semiring S']
  [Semiring S]
  [AddCommMonoid A]
  [AddCommMonoid B]
  [Module S A]
  [Module S B]
  [Module S' A]
  [Module S' B]
  {f : A →ₗ[S] B} [IsBiscalar S S' f]
-- given
  (a : A) :
-- imply
  LinearMap.changeScalars S' f a = f a := by
-- proof
  simp [LinearMap.changeScalars]


-- created on 2026-11-13
