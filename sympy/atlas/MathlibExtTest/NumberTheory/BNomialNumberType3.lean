/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BNomialNumberType3.lean -/


import sympy.atlas.NumberTheory.BNomialNumberType3


namespace MetaMathlibExt

example : bNomialIndispensableDigitCount (fun _ : Fin 1 ↦ (1 : Fin 2)) = 1 := by decide

example : bNomialIndispensableDigitCount (fun _ : Fin 1 ↦ (0 : Fin 2)) = 0 := by decide

example : bNomialNumberType3 2 (by decide) 0 0 = 1 := by decide

example : bNomialNumberType3 2 (by decide) 0 (-1) = 0 := by decide

/- The `b = 3`, `n = 2` row displayed immediately after Definition 9 in the source. -/
example : bNomialNumberType3 3 (by decide) 2 0 = 1 := by decide

example : bNomialNumberType3 3 (by decide) 2 1 = 5 := by decide

example : bNomialNumberType3 3 (by decide) 2 2 = 3 := by decide

#print axioms MetaMathlibExt.bNomialDigitAtOrZero
#print axioms MetaMathlibExt.IsBNomialIndispensableDigit
#print axioms MetaMathlibExt.bNomialIndispensableDigitCount
#print axioms MetaMathlibExt.bNomialNumberType3

end MetaMathlibExt
