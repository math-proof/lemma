import stdlib.SEq
import sympy.Basic
import sympy.tensor.tensor


@[main, cast]
private lemma main
  [Zero α]
  {s : List ℕ}
-- given
  (h_s : s = s')
  (X : Tensor α s)
  (d : Fin s'.length)
  (n : ℕ) :
-- imply
  (cast (congrArg (Tensor α) h_s) X).resize d n ≃ X.resize ⟨d, by grind⟩ n := by
-- proof
  subst h_s
  simp
  rfl


-- created on 2026-07-10
