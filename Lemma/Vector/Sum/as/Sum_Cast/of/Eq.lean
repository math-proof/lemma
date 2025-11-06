import Lemma.Vector.SEq.of.All_EqGetS.Eq
import stdlib.SEq
open Vector


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (h : n = n')
  (s : Finset ι)
  (x : ι → List.Vector α n) :
-- imply
  ∑ i ∈ s, x i ≃ ∑ i ∈ s, cast (congrArg (List.Vector α) h) (x i) := by
-- proof
  apply SEq.of.All_EqGetS.Eq h
  intro i
  sorry


-- created on 2025-11-06
