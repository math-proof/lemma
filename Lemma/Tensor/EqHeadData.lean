import sympy.Basic
import sympy.tensor.tensor


@[main]
private lemma main
-- given
  (x : α) :
-- imply
  (x : Tensor α []).data.head = x := by
-- proof
  rfl


@[main]
private lemma nat
  [NatCast α]
-- given
  (x : ℕ) :
-- imply
  (x : Tensor α []).data.head = x := by
-- proof
  rfl


-- created on 2025-12-30
