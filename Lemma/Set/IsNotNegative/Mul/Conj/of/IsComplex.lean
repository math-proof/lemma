import sympy.functions.elementary.complexes
import sympy.Basic


@[path]
private lemma main
  {x : ℂ}
-- given
  (_h : x ∈ (Set.univ : Set ℂ)) :
-- imply
  x * ~x ∈ Complex.ofReal '' Set.Ici 0 :=
-- proof
  ⟨Complex.normSq x, Complex.normSq_nonneg x, (Complex.mul_conj x).symm⟩


-- created on 2023-05-03
