import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {a : ℂ}
-- given
  (h : a ≠ 0) :
-- imply
  ~a ≠ 0 :=
-- proof
  fun h' => h ((map_eq_zero (starRingEnd ℂ)).mp h')


-- created on 2023-05-02
