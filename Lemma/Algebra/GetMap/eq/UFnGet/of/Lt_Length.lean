import Lemma.Basic


@[main]
private lemma main
  {β : Type*}
  {v : List α}
  {f : α → β}
-- given
  (h : i < v.length) :
-- imply
  have : i < (v.map f).length := by rwa [List.length_map]
  (v.map f)[i] = f v[i] := by
-- proof
  simp


-- created on 2025-06-14
