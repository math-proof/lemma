/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BellMatrix.lean -/


module

public import Def.NumberTheory.BellMatrix
public import Theorem.MathlibExtTest.NumberTheory.BellMatrix

@[expose] public section

namespace MetaMathlibExt

noncomputable def identityBellMatrix (R : Type*) [CommRing R] : BellMatrix R where
  g := 1
  isUnit_const := by simp

end MetaMathlibExt
