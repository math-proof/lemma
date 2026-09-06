import sympy.vector.vector
import Lemma.List.Prod.eq.ProdFinLength_Get
open List


@[main, fin]
private lemma main
  [CommMonoid α]
-- given
  (v : List.Vector α n) :
-- imply
  v.prod = ∏ i : Fin n, v[i] := by
-- proof
  obtain ⟨v, h⟩ := v
  unfold List.Vector.prod
  simp
  rw [Prod.eq.ProdFinLength_Get v]
  congr
  aesop


-- created on 2026-09-06
