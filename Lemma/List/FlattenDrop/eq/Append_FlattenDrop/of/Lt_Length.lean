import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
open List


@[main]
private lemma main
  {i : ℕ}
  {v : List (List α)}
-- given
  (h : i < v.length) :
-- imply
  (v.drop i).flatten = v[i] ++ (v.drop (i + 1)).flatten := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length h]
  rw [List.flatten]


-- created on 2025-06-14
