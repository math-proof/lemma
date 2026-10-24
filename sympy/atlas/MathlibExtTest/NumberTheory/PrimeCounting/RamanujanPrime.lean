/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/PrimeCounting/RamanujanPrime.lean -/


import sympy.atlas.NumberTheory.PrimeCounting.RamanujanPrime

namespace MetaMathlibExt

example {R n : ℕ} (hp : R.Prime)
    (hcount : Nat.primeCounting R - Nat.primeCounting (R / 2) = n) :
    IsRamanujanPrime R n :=
  ⟨hp, hcount⟩

example {R n : ℕ} (h : IsRamanujanPrime R n) : R.Prime := h.1

end MetaMathlibExt
