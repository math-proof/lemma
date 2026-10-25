import Instance.CuspForm_HeckeAlgebra
import Def.HeckeGalois_EichlerShimura

set_option autoImplicit false

noncomputable section

namespace CuspForm

variable (N : ℕ) [NeZero N] (k : ℤ)

def heckeFormsGen (ℓ : Nat.Primes) : heckeAlgebra N k ∅ :=
  if h : (ℓ : ℕ) ∣ N then heckeAlgebra.U ℓ.2 h (Set.notMem_empty _)
  else heckeAlgebra.T ℓ.2 h (Set.notMem_empty _)


def heckeEvalForms : ModularCurve.HeckeAlg →+* heckeAlgebra N k ∅ :=
  (MvPolynomial.aeval (heckeFormsGen N k)).toRingHom

end CuspForm

end
