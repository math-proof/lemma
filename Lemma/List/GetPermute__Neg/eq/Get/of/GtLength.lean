import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
open List


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > d) :
-- imply
  have : 0 < (s.permute ⟨d, h⟩ (-d)).length := by
    simp
    omega
  (s.permute ⟨d, h⟩ (-d))[0] = s[d] := by
-- proof
  have := GetPermute__Neg.eq.Get_Add.of.GtLength_Add (i := 0) (d := d) (s := s) (by omega)
  simp at this
  assumption


-- created on 2025-11-23
