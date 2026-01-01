import Lemma.Fin.Sum.of.All_Eq
import Lemma.Vector.Sum.eq.Sum_Get
open Fin Vector


@[main, fin 2]
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


-- created on 2025-11-06
