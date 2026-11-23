/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Fourier/PrincipalMinor.lean -/

module

public import Def.NumberTheory.Fourier.PrincipalMinor
public import Theorem.Nat.Fourier.PrincipalMinor

@[expose] public section

namespace Fourier

variable {M : ℕ} {R : Type*} [CommRing R]

def rootTwoInt : RootData 2 ℤ where
  zeta := -1
  order_ge := by norm_num
  isPrimitiveRoot := IsPrimitiveRoot.neg_one 0 (by norm_num)

end Fourier
