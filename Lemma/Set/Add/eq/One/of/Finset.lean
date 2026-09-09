import Lemma.Set.Ne.of.Finset
import Lemma.Set.In_Finset.is.OrEqS
open Set


@[main]
private lemma main
  [AddZeroClass α] [One α] [NeZero (1 : α)]
  {x y : α}
-- given
  (h : ({x, y} : Set α) = {0, 1}) :
-- imply
  x + y = 1 := by
-- proof
  have hne := Ne.of.Finset h
  have hx : x ∈ ({0, 1} : Set α) := by simp [← h]
  have hy : y ∈ ({0, 1} : Set α) := by simp [← h]
  rcases OrEqS.of.In_Finset hx with hx | hx
  ·
    rcases OrEqS.of.In_Finset hy with hy | hy
    ·
      exact (hne (hx.trans hy.symm)).elim
    ·
      simp [hx, hy]
  ·
    rcases OrEqS.of.In_Finset hy with hy | hy
    ·
      simp [hx, hy]
    ·
      exact (hne (hx.trans hy.symm)).elim


-- created on 2020-08-27
-- updated on 2026-09-09
