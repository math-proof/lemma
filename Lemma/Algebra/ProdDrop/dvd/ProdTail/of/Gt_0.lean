import Lemma.Algebra.Drop.eq.DropDrop__Sub.of.Ge
import Lemma.Algebra.Tail.eq.Drop_1
import Lemma.Algebra.ProdDrop.dvd.Prod
open Algebra


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
