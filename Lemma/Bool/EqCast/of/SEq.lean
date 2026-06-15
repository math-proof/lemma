import stdlib.SEq
import sympy.Basic


@[main, comm 1]
private lemma main
  {Vector : α → Sort v}
  {a : Vector n}
  {b : Vector m}
-- given
  (h : a ≃ b) :
-- imply
  cast (congrArg Vector h.left) a = b :=
-- proof
  match h with
  | ⟨Eq.refl _, h⟩ => h.eq


-- created on 2025-07-25
