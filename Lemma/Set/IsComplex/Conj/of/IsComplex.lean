import sympy.functions.elementary.complexes
import sympy.Basic
open Complex


@[main]
private lemma main
  {a : ℂ}
-- given
  (_h : a ∈ (Set.univ : Set ℂ)) :
-- imply
  ~a ∈ (Set.univ : Set ℂ) :=
-- proof
  Set.mem_univ _


-- created on 2023-05-03
