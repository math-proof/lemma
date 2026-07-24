import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma cons
  {A B : Tensor α (n :: s)}
  {A' B' : Tensor α (m :: s)}
-- given
  (h : A = B)
  (h' : A' = B') :
-- imply
  A ++ A' = B ++ B' := by
-- proof
  rw [h, h']


@[main]
private lemma main
  {A B : Tensor α (bz ++ n :: s)}
  {A' B' : Tensor α (bz ++ m :: s)}
-- given
  (h : A = B)
  (h' : A' = B') :
-- imply
  A ++ A' = B ++ B' := by
-- proof
  rw [h, h']


-- created on 2026-01-13
