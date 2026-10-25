/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BellMatrix.lean -/


import Def.NumberTheory.BellMatrix
import Def.MathlibExtTest.NumberTheory.BellMatrix


namespace MetaMathlibExt

example {R : Type*} [CommRing R] : (identityBellMatrix R).h = PowerSeries.X := by
  simp [identityBellMatrix, BellMatrix.h]

example {R : Type*} [CommRing R] : (identityBellMatrix R).entry 0 0 = 1 := by
  simp [identityBellMatrix, BellMatrix.entry]

#print axioms MetaMathlibExt.BellMatrix
#print axioms MetaMathlibExt.BellMatrix.h
#print axioms MetaMathlibExt.BellMatrix.entry

end MetaMathlibExt
