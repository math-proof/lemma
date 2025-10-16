import stdlib.List
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.GetElem.eq.SomeGet.of.Lt_Length
import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.GetDrop.eq.Get_Add.of.Add.lt.Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Nat.Gt_0
import Lemma.Nat.Ge_1.of.Ne_0
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.List.LengthDrop.eq.SubLength
open List Bool Nat


@[main]
private lemma main
  {s : List α}
-- given
  (i : Fin s.length) :
-- imply
  (s.permute i ↑(s.length - 1 - i)).drop (s.length - 1) = [s[i]] := by
-- proof
  ext j
  by_cases h_j : j = 0
  ·
    subst h_j
    have := Gt_0 i
    repeat rw [GetElem.eq.SomeGet.of.Lt_Length]
    ·
      apply IffEqS.of.Eq
      apply congrArg
      rw [GetDrop.eq.Get_Add.of.Add.lt.Length]
      ·
        conv_rhs =>
          simp
        conv_lhs =>
          arg 2
          simp
        rw [GetPermute.eq.Ite.of.Lt_Length.Lt_Length (by omega)]
        ·
          split_ifs with h_i h_i_lt h_i_eq
          repeat omega
          ·
            rfl
          ·
            omega
        ·
          omega
      ·
        rw [LengthPermute.eq.Length]
        omega
    ·
      simp
    .
      simp
      rw [LengthPermute.eq.Length]
      omega
  ·
    have h_j := Ge_1.of.Ne_0 h_j
    repeat rw [GetElem.eq.None.of.Ge_Length]
    ·
      simpa
    ·
      rw [LengthDrop.eq.SubLength]
      rw [LengthPermute.eq.Length]
      omega


-- created on 2025-10-13
