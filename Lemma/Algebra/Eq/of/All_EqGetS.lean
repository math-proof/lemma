import stdlib.List.Vector
import Lemma.Basic


@[main]
private lemma main
  {a b : List.Vector α n}
-- given
  (h : ∀ i : Fin n, a[i] = b[i]) :
-- imply
  a = b := by
-- proof
  aesop


-- created on 2025-07-11
