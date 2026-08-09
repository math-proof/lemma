import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetElem.eq.SomeGet.of.GtLength
import Lemma.List.GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0
import Lemma.List.Swap
open List


@[main]
private lemma main
-- given
  (s : List α)
  (i j : Fin s.length) :
-- imply
  (s.swap i j)[i]? = some s[j] := by
-- proof
  have := LengthSwap.eq.Length s i j
  have h_i : i < (s.swap i j).length := by
    rw [this]
    simp
  have h_some := GetElem.eq.SomeGet.of.GtLength h_i
  simp [h_some]
  unfold List.swap
  split_ifs with h_eq h_lt? h_j h_i
  ·
    simp [h_eq]
  ·
    simp
  ·
    grind
  ·
    have h_le := Nat.Le.of.NotGt h_lt?
    have h_ne := Bool.Ne.of.NotEq h_eq
    have h_lt := Nat.Lt.of.Le.Ne h_le h_ne.symm
    simp_all
    rw [GetCons.eq.Get_Sub_1.of.Lt_Add_1.Gt_0]
    ·
      have h_length_slice := LengthSlice.eq.SubMin_Length s (j + 1) i
      grind
    ·
      grind
  ·
    grind


@[main]
private lemma left
-- given
  (s : List α)
  (i j : Fin s.length) :
-- imply
  (s.swap i j)[j]? = some s[i] := by
-- proof
  rw [Swap]
  rw [main]


-- created on 2025-05-15
-- updated on 2025-05-17
