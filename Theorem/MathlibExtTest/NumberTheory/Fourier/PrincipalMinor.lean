/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Fourier/PrincipalMinor.lean -/


import Def.NumberTheory.Fourier.PrincipalMinor
import Lemma.Nat.Fourier.PrincipalMinor
import Def.MathlibExtTest.NumberTheory.Fourier.PrincipalMinor


namespace Fourier

variable {M : ℕ} {R : Type*} [CommRing R]

example (root : RootData M R) (S : Finset (ZMod M)) (i j : S) :
    principalMinorMatrix M root S i j = root.zeta ^ (i.val * j.val).val := by
  simp

example (root : RootData M R) : principalMinorDet M root ∅ = 1 := by
  simp

example (root : RootData M R) (a : ZMod M) :
    principalMinorDet M root {a} = root.zeta ^ (a * a).val := by
  simp

example : principalMinorDet 2 rootTwoInt ({1} : Finset (ZMod 2)) = -1 := by
  rw [principalMinorDet_singleton]
  change (-1 : ℤ) ^ 1 = -1
  norm_num

end Fourier
