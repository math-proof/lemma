import stdlib.SEq
import sympy.Basic
import sympy.tensor.Basic


@[main, cast]
private lemma main
-- given
  (h : s = s')
  (X : Tensor α s)
  (i j : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h) X).transpose i j ≃ X.transpose i j := by
-- proof
  subst h
  rfl


@[main, cast]
private lemma t
-- given
  (h : s = s')
  (X : Tensor α s) :
-- imply
  (cast (congrArg (Tensor α) h) X)ᵀ ≃ Xᵀ := by
-- proof
  subst h
  rfl


-- created on 2026-07-11
