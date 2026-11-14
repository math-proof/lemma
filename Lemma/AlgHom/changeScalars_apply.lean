import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.IsModuleTopology


@[path]
private lemma main
  [CommSemiring A] [CommSemiring B] [CommSemiring S'] [CommSemiring S] [Algebra S A]
  [Algebra S B] [Algebra S' A] [Algebra S' B]
  {f : A →ₐ[S] B} [IsBiscalar S S' f]
-- given
  (a : A) :
-- imply
  AlgHom.changeScalars S' f a = f a := by
-- proof
  simp [AlgHom.changeScalars]


-- created on 2026-11-13
