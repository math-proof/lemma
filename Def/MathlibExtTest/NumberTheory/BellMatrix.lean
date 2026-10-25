/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BellMatrix.lean -/


import Def.NumberTheory.BellMatrix
import Theorem.MathlibExtTest.NumberTheory.BellMatrix


namespace MetaMathlibExt

noncomputable def identityBellMatrix (R : Type*) [CommRing R] : BellMatrix R where
  g := 1
  isUnit_const := by simp

end MetaMathlibExt
