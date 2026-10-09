import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (_h : x ∈ (Set.univ : Set ℂ)) :
-- imply
  x + (starRingEnd ℂ) x ∈ Set.range Complex.ofReal :=
-- proof
  ⟨2 * x.re, (Complex.add_conj x).symm⟩


-- created on 2023-05-25
