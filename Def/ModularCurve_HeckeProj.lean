import Def.HeckeGalois_EichlerShimura
import Instance.CuspForm_HeckeAlgebra

noncomputable section

namespace ModularCurve

variable (N : ℕ) [NeZero N]

def heckeProjGen (ℓ : Nat.Primes) : CuspForm.heckeAlgebra N 2 ∅ :=
  if h : (ℓ : ℕ) ∣ N then CuspForm.heckeAlgebra.U ℓ.2 h (Set.notMem_empty _)
  else CuspForm.heckeAlgebra.T ℓ.2 h (Set.notMem_empty _)

def heckeProj : HeckeAlg →+* CuspForm.heckeAlgebra N 2 ∅ :=
  (MvPolynomial.aeval (R := ℤ) (heckeProjGen N)).toRingHom

end ModularCurve

end
