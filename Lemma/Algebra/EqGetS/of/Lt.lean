import Lemma.Basic


@[main]
private lemma main
  {v : List.Vector α n}
  {i : ℕ}
-- given
  (h : i < n) :
-- imply
  v[i] = v.get ⟨i, h⟩ := by
-- proof
  simp [GetElem.getElem]


-- created on 2025-07-10
