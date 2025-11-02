import Lemma.List.GetPermute.eq.Get.of.GtLength_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List α}
  {i j : Fin s.length}
-- given
  (h : j ≥ i) :
-- imply
  (s.permute i (j - i : ℕ))[j]'(by simp) = s[i] := by
-- proof
  have := GetPermute.eq.Get.of.GtLength_Add (s := s) (i := i) (d := j - i) (by omega)
  simp [EqAdd_Sub.of.Ge h] at this
  assumption


-- created on 2025-10-31
