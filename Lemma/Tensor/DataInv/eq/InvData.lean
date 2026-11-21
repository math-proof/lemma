import Instance.Data.Tensor.Defs.Part2


@[path]
private lemma main
  [Inv α]
-- given
  (X : Tensor α s) :
-- imply
  X⁻¹.data = X.data⁻¹ :=
-- proof
  rfl


-- created on 2025-10-04
-- updated on 2026-11-20
