import Lemma.Algebra.Drop.eq.Cons_Drop_Add_1.of.Lt_Length
import Lemma.Algebra.TakeCons.eq.List
open Algebra


@[main]
private lemma main
  {v : List α}
-- given
  (h : i < v.length) :
-- imply
  (v.drop i).take 1 = [v[i]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.Lt_Length (by assumption)]
  rw [TakeCons.eq.List]


-- created on 2025-06-14
