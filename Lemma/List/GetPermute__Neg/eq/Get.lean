import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
open List


@[main]
private lemma main
  {s : List α}
-- given
  (d : Fin s.length) :
-- imply
  have : 0 < (s.permute d (-d)).length := by
    simp
    linarith [d.isLt]
  (s.permute d (-d))[0] = s[d] := by
-- proof
  have := GetPermute__Neg.eq.Get_Add.of.GtLength_Add (i := 0) (d := d) (s := s) (by omega)
  simp_all


-- created on 2025-11-23
