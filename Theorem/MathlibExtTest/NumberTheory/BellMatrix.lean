/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/BellMatrix.lean -/


import Def.NumberTheory.BellMatrix


namespace MetaMathlibExt

example {R : Type*} [CommRing R] (M : BellMatrix R) :
    M.h = PowerSeries.X * M.g := rfl

example {R : Type*} [CommRing R] (M : BellMatrix R) (n : ℕ) :
    M.entry n 0 = M.g.coeff n := by
  simp [BellMatrix.entry]

end MetaMathlibExt
