import Lemma.Set.InAdd.of.In_Ico
import Lemma.Algebra.EqAddSub
open Set Algebra


@[main]
private lemma offset
  [Preorder ι]
  [AddGroup ι]
  [AddLeftMono ι]
  [AddRightMono ι]
  [AddLeftStrictMono ι]
  [AddRightStrictMono ι]
  {f : ι → Prop}
  {a m : ι}
-- given
  (h : ∀ n ∈ Ico a m, f n) :
-- imply
  ∀ n ∈ Ico (a - d) (m - d), f (n + d) := by
-- proof
  intro n hn
  apply h (n + d)
  have h := InAdd.of.In_Ico hn d
  convert h
  repeat rw [EqAddSub]


-- created on 2025-08-02
