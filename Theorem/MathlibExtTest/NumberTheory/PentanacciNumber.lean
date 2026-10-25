/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PentanacciNumber.lean -/


import Def.NumberTheory.PentanacciNumber


namespace MetaMathlibExt

example : pentanacciNumber 0 = 1 := rfl

example : pentanacciNumber 4 = 8 := rfl

example : pentanacciNumber 5 = 16 := rfl

example : pentanacciNumber 6 = 31 := rfl

#print axioms pentanacciNumber

end MetaMathlibExt
