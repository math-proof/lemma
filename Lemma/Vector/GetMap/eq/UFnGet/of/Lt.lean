import sympy.Basic


@[main]
private lemma main
  {β : Type*}
-- given
  (h : i < n)
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (v.map f)[i] = f v[i] := by
-- proof
  simp [GetElem.getElem]


@[main]
private lemma fin
  {β : Type*}
-- given
  (h : i < n)
  (v : List.Vector α n)
  (f : α → β) :
-- imply
  (v.map f).get ⟨i, h⟩ = f (v.get ⟨i, h⟩) := by
-- proof
  apply main


-- created on 2025-06-01
-- updated on 2025-06-14
