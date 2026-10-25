/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/LucasPolytopicNumber.lean -/


import Def.NumberTheory.LucasPolytopicNumber.Part2
import Lemma.Nat.LucasPolytopicNumber
import Mathlib.Tactic
import Def.MathlibExtTest.NumberTheory.LucasPolytopicNumber


namespace MetaMathlibExt

example : lucasBracket naturalLucasParameters 0 = 0 := by
  norm_num [lucasBracket, lucasBracketAux]

example : lucasBracket naturalLucasParameters 4 = 4 := by
  simpa [lucasBracket, naturalLucasParameters] using naturalLucasBracketAux 4

example : lucasnomial naturalLucasParameters 4 2 = 6 := by
  norm_num [lucasnomial, lucasFactorial, Finset.prod_range_succ, lucasBracket,
    lucasBracketAux, naturalLucasParameters]

example : lucasPolytopicNumber naturalLucasParameters 0 2 = 0 := by
  norm_num [lucasPolytopicNumber]

/-- The former parameter domain admitted this zero bracket, which made
`lucasnomial 4 3` silently evaluate the undefined quotient `0 / 0` as zero.
It is now excluded by `LucasParameters.bracket_ne_zero`. -/
example : lucasBracketAux 1 (-1) 3 = 0 := by
  norm_num [lucasBracketAux]

example : ¬∃ P : LucasParameters, P.s = 1 ∧ P.t = -1 := by
  rintro ⟨P, hs, ht⟩
  have hne := P.bracket_ne_zero 3 (by norm_num)
  apply hne
  simp [hs, ht, lucasBracketAux]

#print axioms lucasBracket
#print axioms lucasFactorial
#print axioms lucasnomial
#print axioms lucasnomial_eq_zero_of_lt
#print axioms lucasPolytopicNumber
#print axioms lucasTriangularNumber
#print axioms lucasTetrahedralNumber
#print axioms lucasPentachoronNumber
#print axioms lucasHexateronNumber

end MetaMathlibExt
