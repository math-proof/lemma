import Def.CerednikDrinfeld_JPrimeTorsionDatum
import Instance.Compat_Mathlib430

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]

def ribbonGramModP (p : ℕ) (D : DegeneracyData E V) (x : ↥(ribbonKernel D)) :
    ↥(ribbonKernel D) →ₗ[ℤ] ZMod p :=
  (Int.castAddHom (ZMod p)).toIntLinearMap ∘ₗ (ribbonGram D x)

end CerednikDrinfeld

end
