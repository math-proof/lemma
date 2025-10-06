import Lemma.Set.EqUnionInter__SDiff
import Lemma.Set.IffInS.of.Eq
import Lemma.Set.In_Union.is.OrInS
open Set


@[main]
private lemma fin
  [DecidableEq ι]
-- given
  (A B : Finset ι)
  (x : ι) :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff.fin (s := A) (t := B)
  have := IffInS.of.Eq.fin this x
  rw [In_Union.is.OrInS.fin] at this
  rwa [Iff.comm]


@[main]
private lemma main
-- given
  (A B : Set α)
  (x : α) :
-- imply
  x ∈ A ↔ x ∈ A ∩ B ∨ x ∈ A \ B := by
-- proof
  have := EqUnionInter__SDiff (s := A) (t := B)
  have := IffInS.of.Eq this x
  rw [In_Union.is.OrInS] at this
  rwa [Iff.comm]


-- created on 2025-04-30
-- updated on 2025-05-01
