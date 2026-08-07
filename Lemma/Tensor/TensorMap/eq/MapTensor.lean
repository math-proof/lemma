import sympy.tensor.Basic
import sympy.Basic


@[main]
private lemma main
  {s : List ℕ}
-- given
  (v : List.Vector α s.prod)
  (f : α → β) :
-- imply
  (⟨v.map f⟩ : Tensor β s) = (⟨v⟩ : Tensor α s).map f := by
-- proof
  simp [Tensor.map]


-- created on 2026-08-07
