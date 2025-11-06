import Lemma.Finset.NeUnivEmpty.of.Gt_0
import Lemma.Vector.SEqSumS.of.All_SEq.Ne_Empty
import stdlib.SEq
import sympy.vector.vector
open Finset Vector


@[main]
private lemma main
  [AddCommMonoid α]
  {x : Fin m → List.Vector α n}
  {y : Fin m → List.Vector α n'}
-- given
  (h_m : m > 0)
  (h : ∀ i : Fin m, x i ≃ y i) :
-- imply
  ∑ i : Fin m, x i ≃ ∑ i : Fin m, y i := by
-- proof
  apply SEqSumS.of.All_SEq.Ne_Empty (s := Finset.univ)
  ·
    apply NeUnivEmpty.of.Gt_0 h_m
  ·
    aesop


-- created on 2025-11-05
-- updated on 2025-11-06
