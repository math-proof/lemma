import sympy.Basic


@[main]
private lemma main
  [AddCommMonoid α]
-- given
  (s : List α) :
-- imply
  s.sum = ∑ i : Fin s.length, s[i] := by
-- proof
  conv in s.sum =>
    rw [← List.ofFn_get s]
  rw [List.sum_ofFn]
  congr


-- created on 2025-07-14
