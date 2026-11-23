/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/IntegerComplexity.lean -/

module

public import Def.NumberTheory.IntegerComplexity.Part3
public import Theorem.Nat.IntegerComplexity

@[expose] public section

open IntegerComplexity
open IntegerComplexity.Expr


-- C1-C3: explicit parenthesized expression for 6 with five ones
-- (1+1)*(1+1+1) = 2*3 = 6
def expr6 : Expr := .mul (.add .one .one) (.add (.add .one .one) .one)

