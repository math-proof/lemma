import Lemma.Algebra.EqAddSub
import Lemma.Set.InSub.of.In_Ico
open Algebra Set


@[main]
private lemma offset
  [OrderedAddCommGroup ι]
  {f : ι → Prop}
  {a m : ι}
-- given
  (h : ∃ n ∈ Ico a m, f n)
  (d : ι) :
-- imply
  ∃ n ∈ Ico (a - d) (m - d), f (n + d) := by
-- proof
  obtain ⟨n, hn, fn⟩ := h
  use n - d
  constructor
  ·
    apply InSub.of.In_Ico hn d
  ·
    rwa [EqAddSub]


-- created on 2025-08-02
