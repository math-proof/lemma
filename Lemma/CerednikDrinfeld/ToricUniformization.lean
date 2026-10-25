import Def.CerednikDrinfeld_JPrimeTorsionDatum
import Lemma.Compat.Mathlib430
import Def.CerednikDrinfeld_ToricUniformization
import Structure.CerednikDrinfeld_ToricUniformization

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type} [Fintype E] [Fintype V] [DecidableEq V]


omit [Fintype V] in
@[simp] theorem ribbonGramModP_apply (p : ℕ) (D : DegeneracyData E V) (x y : ↥(ribbonKernel D)) :
    ribbonGramModP p D x y = ((ribbonGram D x y : ℤ) : ZMod p) := rfl


end CerednikDrinfeld

end
