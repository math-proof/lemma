/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/IntegerComplexity.lean -/


import Def.NumberTheory.IntegerComplexity.Part3
import Lemma.Nat.IntegerComplexity
open IntegerComplexity
open IntegerComplexity.Expr


-- C1-C3: explicit parenthesized expression for 6 with five ones
-- (1+1)*(1+1+1) = 2*3 = 6
def expr6 : Expr := .mul (.add .one .one) (.add (.add .one .one) .one)

