/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Fourier/PrincipalMinor.lean -/


import Def.NumberTheory.Fourier.PrincipalMinor
import Lemma.Nat.Fourier.PrincipalMinor


namespace Fourier

variable {M : ℕ} {R : Type*} [CommRing R]

def rootTwoInt : RootData 2 ℤ where
  zeta := -1
  order_ge := by norm_num
  isPrimitiveRoot := IsPrimitiveRoot.neg_one 0 (by norm_num)

end Fourier
