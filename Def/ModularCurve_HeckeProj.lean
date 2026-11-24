module
public import Def.HeckeGalois_EichlerShimura
public import Instance.CuspForm_HeckeAlgebra


public section

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
