import Lemma.List.DropPermute.eq.Drop.of.Add.lt.Length


@[main]
private lemma main
  [Monoid α]
-- given
  (s : List α)
  (i : Fin s.length)
  (d : ℕ) :
-- imply
  (s.drop i).take (d + 1) = (((s.permute i d).take (d + i + 1)).drop i).rotate d := by
-- proof
  sorry


-- created on 2025-10-15
