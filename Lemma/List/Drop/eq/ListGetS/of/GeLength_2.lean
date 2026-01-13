import Lemma.List.Drop.eq.Cons_Drop_Add_1.of.GtLength
import Lemma.List.Drop.eq.ListGet.of.GeLength_1
import Lemma.List.EqConsS.is.Eq.Eq
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length ≥ 2) :
-- imply
  s.drop (s.length - 2) = [s[s.length - 2], s[s.length - 1]] := by
-- proof
  rw [Drop.eq.Cons_Drop_Add_1.of.GtLength (by omega)]
  apply EqConsS.of.Eq.Eq
  ·
    rfl
  ·
    simp [show s.length - 2 + 1 = s.length - 1 by omega]
    apply Drop.eq.ListGet.of.GeLength_1
    omega


-- created on 2026-01-03
