import Lemma.Fin.Sum.of.All_Eq
import Lemma.Vector.Sum.eq.Sum_Get
open Fin Vector


@[main]
private lemma main
  [AddCommMonoid α]
  {x : List.Vector α n}
  {y : List.Vector α n'}
-- given
  (h_n : n = n')
  (h : ∀ i : Fin n, x[i] = y[i]'(by grind)) :
-- imply
  x.sum = y.sum := by
-- proof
  repeat rw [Sum.eq.Sum_Get]
  rw [Sum.of.All_Eq h]
  aesop


@[main]
private lemma fin
  [AddCommMonoid α]
  {x : List.Vector α n}
  {y : List.Vector α n'}
-- given
  (h_n : n = n')
  (h : ∀ i : Fin n, x.get i = y.get ⟨i, by grind⟩) :
-- imply
  x.sum = y.sum :=
-- proof
  main h_n h


-- created on 2025-11-06
