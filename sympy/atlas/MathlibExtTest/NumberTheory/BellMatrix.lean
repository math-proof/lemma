/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BellMatrix.lean -/


import sympy.atlas.NumberTheory.BellMatrix


namespace MetaMathlibExt

example {R : Type*} [CommRing R] (M : BellMatrix R) :
    M.h = PowerSeries.X * M.g := rfl

example {R : Type*} [CommRing R] (M : BellMatrix R) (n : ℕ) :
    M.entry n 0 = M.g.coeff n := by
  simp [BellMatrix.entry]

private noncomputable def identityBellMatrix (R : Type*) [CommRing R] : BellMatrix R where
  g := 1
  isUnit_const := by simp

example {R : Type*} [CommRing R] : (identityBellMatrix R).h = PowerSeries.X := by
  simp [identityBellMatrix, BellMatrix.h]

example {R : Type*} [CommRing R] : (identityBellMatrix R).entry 0 0 = 1 := by
  simp [identityBellMatrix, BellMatrix.entry]

#print axioms MetaMathlibExt.BellMatrix
#print axioms MetaMathlibExt.BellMatrix.h
#print axioms MetaMathlibExt.BellMatrix.entry

end MetaMathlibExt
