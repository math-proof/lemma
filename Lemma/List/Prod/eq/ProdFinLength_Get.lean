import sympy.Basic


@[main]
private lemma main
  [CommMonoid α]
-- given
  (s : List α) :
-- imply
  s.prod = ∏ i : Fin s.length, s[i] := by
-- proof
  conv in s.prod =>
    rw [← List.ofFn_get s]
  rw [List.prod_ofFn]
  congr


-- created on 2026-09-06
