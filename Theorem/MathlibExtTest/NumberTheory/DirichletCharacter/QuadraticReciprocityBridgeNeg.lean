/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/DirichletCharacter/QuadraticReciprocityBridgeNeg.lean -/


import Lemma.Nat.DirichletCharacter.QuadraticReciprocityBridgeNeg
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.Prime
open MetaMathlibExt


example :
    jacobiSym ((3 : ℕ) : ℤ) (-7 : ℤ).natAbs = kroneckerSym (-7 : ℤ) 3 :=
  jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg
    (-7) 3 (by norm_num) (by decide) (by decide) (by decide)

example :
    jacobiSym ((7 : ℕ) : ℤ) (13 : ℤ).natAbs = kroneckerSym (13 : ℤ) 7 :=
  jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four
    13 7 (by norm_num) (by decide) (by decide)

#print axioms MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four_neg
#print axioms MetaMathlibExt.jacobiSym_natAbs_eq_kroneckerSym_of_prime_ne_two_of_one_mod_four

