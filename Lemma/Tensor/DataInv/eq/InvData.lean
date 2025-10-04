import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  [Inv α]
-- given
  (X : Tensor α s) :
-- imply
  X⁻¹.data = X.data⁻¹ :=
-- proof
  rfl


-- created on 2025-10-04
