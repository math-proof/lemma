import Lemma.List.GetPermute__Neg.eq.Get_Add.of.GtLength_Add
import Lemma.Nat.EqAddSub.of.Ge
open List Nat


@[main, comm]
private lemma main
  {s : List α}
-- given
  (h : s.length > i)
  (h_d : i ≥ d) :
-- imply
  have : i - d < (s.permute ⟨i, h⟩ (-d)).length := by
    simp
    omega
  (s.permute ⟨i, h⟩ (-d))[i - d] = s[i] := by
-- proof
  have := GetPermute__Neg.eq.Get_Add.of.GtLength_Add (s := s) (i := i - d) (d := d) (by omega)
  simp [EqAddSub.of.Ge h_d] at this
  assumption


-- created on 2025-11-15
