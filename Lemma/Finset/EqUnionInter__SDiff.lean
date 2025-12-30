import Lemma.Finset.EqUnionSDiff__Inter
import Lemma.Finset.Union
open Finset


@[main]
private lemma main
  [DecidableEq ι]
-- given
  (s t : Finset ι) :
-- imply
  s ∩ t ∪ s \ t = s := by
-- proof
  have := EqUnionSDiff__Inter (s := s) (t := t)
  rwa [Union.comm] at this


-- created on 2025-12-30
