import Lemma.Set.EqUnionSDiff__Inter
import Lemma.Set.Union
open Set


@[main]
private lemma fin
  [DecidableEq ι]
-- given
  (s t : Finset ι) :
-- imply
  s ∩ t ∪ s \ t = s := by
-- proof
  have := EqUnionSDiff__Inter.fin (s := s) (t := t)
  rw [Union.comm.finset] at this
  assumption


@[main]
private lemma main
-- given
  (s t : Set α) :
-- imply
  s ∩ t ∪ s \ t = s :=
-- proof
  Set.inter_union_diff s t


-- created on 2025-04-30
-- updated on 2025-07-20
