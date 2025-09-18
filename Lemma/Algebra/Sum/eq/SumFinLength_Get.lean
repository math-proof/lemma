import Lemma.Basic


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (v : List α) :
-- imply
  v.sum = ∑ i : Fin v.length, v[i] := by
-- proof
  conv in v.sum =>
    rw [← List.ofFn_get v]
  rw [List.sum_ofFn]
  congr


-- created on 2025-07-14
