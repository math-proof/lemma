import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
open List


@[main]
private lemma main
  {i : ℕ}
  {s : List (List α)}
-- given
  (h : i < s.length) :
-- imply
  (s.drop i).flatten = s[i] ++ (s.drop (i + 1)).flatten := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length h]
  rw [List.flatten]


-- created on 2025-06-14
