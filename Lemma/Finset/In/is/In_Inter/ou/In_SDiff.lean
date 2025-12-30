import Lemma.Finset.EqUnionInter__SDiff
import Lemma.Finset.IffInS.of.Eq
import Lemma.Finset.In_Union.is.OrInS
import Lemma.Set.EqUnionInter__SDiff
open Set Finset


@[main]
private lemma main
  [DecidableEq ι]
-- given
  (A B : Finset ι)
  (x : ι) :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff (s := A) (t := B)
  have := IffInS.of.Eq this x
  rw [In_Union.is.OrInS] at this
  rwa [Iff.comm]


-- created on 2025-12-30
