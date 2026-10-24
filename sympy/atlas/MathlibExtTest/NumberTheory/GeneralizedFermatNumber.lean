/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/GeneralizedFermatNumber.lean -/


import sympy.atlas.NumberTheory.GeneralizedFermatNumber


example : MetaMathlibExt.generalizedFermatNumber 2 1 (by decide) (by decide) = 5 := rfl
example : MetaMathlibExt.generalizedFermatNumber 4 2 (by decide) (by decide) = 257 := rfl

example (b n : ℕ) (hb : Even b) (hn : 0 < n) :
    MetaMathlibExt.generalizedFermatNumber b n hb hn = b ^ (2 ^ n) + 1 := rfl

example (b n : ℕ) (hb₁ hb₂ : Even b) (hn₁ hn₂ : 0 < n) :
    MetaMathlibExt.generalizedFermatNumber b n hb₁ hn₁ =
      MetaMathlibExt.generalizedFermatNumber b n hb₂ hn₂ := rfl

#print axioms MetaMathlibExt.generalizedFermatNumber
