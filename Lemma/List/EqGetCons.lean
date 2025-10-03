import sympy.Basic


@[main]
private lemma main
-- given
  (head : List.Vector α n)
  (tail : List.Vector (List.Vector α n) m) :
-- imply
  (head ::ᵥ tail)[0] = head := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-05-08
