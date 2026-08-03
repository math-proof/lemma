import sympy.functions.elementary.complexes
import sympy.sets.sets
import sympy.Basic


@[main]
private lemma main
-- given
  (z : ℂ) :
-- imply
  arg z ∈ Ioc (-Real.pi) Real.pi :=
-- proof
  Complex.arg_mem_Ioc z


-- created on 2025-01-05
