import sympy.tensor.Basic
import Lemma.Basic


@[main]
private lemma main
-- given
  (X : Tensor α [m, n].tail.tail) :
-- imply
  have h : Tensor α [m, n].tail.tail = Tensor α [] := by simp
  X = cast h (⟨X.data⟩ : Tensor α []) := by
-- proof
  let ⟨data⟩ := X
  simp


-- created on 2025-07-19
