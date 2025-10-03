import Lemma.List.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.List.Tail.eq.Drop_1
import Lemma.List.ProdDrop.dvd.Prod
open List


@[main]
private lemma main
  {d : ℕ}
-- given
  (h_d : d > 0)
  (s : List ℕ):
-- imply
  (s.drop d).prod ∣ s.tail.prod := by
-- proof
  rw [Drop.eq.DropDrop__Sub.of.Ge (k := d) (i := 1) (by linarith)]
  rw [Drop_1.eq.Tail]
  apply ProdDrop.dvd.Prod


-- created on 2025-07-08
-- updated on 2025-07-09
