import Lemma.List.EraseIdxPermute.eq.EraseIdx.of.GtLength_Add
import Lemma.Nat.EqAdd_Sub.of.Ge
open List Nat


@[main]
private lemma main
  {s : List ℕ}
  {i j : Fin s.length}
-- given
  (h : j ≥ i) :
-- imply
  (s.permute i (j - i : ℕ)).eraseIdx j = s.eraseIdx i := by
-- proof
  have := EraseIdxPermute.eq.EraseIdx.of.GtLength_Add (s := s) (i := i) (d := j - i) (by omega)
  simp [EqAdd_Sub.of.Ge h] at this
  assumption


-- created on 2025-10-31
