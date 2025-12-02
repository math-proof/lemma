import Lemma.List.GetPermute__Neg.eq.Ite.of.GtLength
open List


@[main]
private lemma main
  {s : List α}
  {i : Fin s.length}
  {d : ℕ}
-- given
  (h_d : i > d) :
-- imply
  have : 0 < (s.permute i (-d)).length := by
    simp
    linarith [i.isLt]
  (s.permute i (-d))[0] = s[0] := by
-- proof
  simp [GetPermute__Neg.eq.Ite.of.GtLength (s := s) (t := 0) (by omega) i d]
  omega


-- created on 2025-12-02
