-- Carved from Lemma/Definitions/Def_CuspForm_TWLevelHeckeModule.lean: instance decls only.
import Mathlib
import Instance.CuspForm_AuxLevelHeckeModule
import Inductive.CuspForm_TWLevelHeckeModule_Gen
import Lemma.CuspForm.TWLevelHeckeModule

set_option autoImplicit false

noncomputable section

namespace CuspForm.TWLevel

section Level

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ)

instance level_neZero [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] : NeZero (level N r qv) :=
  ⟨mul_ne_zero (mul_ne_zero (NeZero.ne N)
    (Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (qv i))) (NeZero.ne r)⟩

end Level

section Ops

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪]

instance instModuleFreeAlgCarrier [NeZero N] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]
    (θ : ↥(CuspForm.heckeAlgebra N 2 S) →+* IsLocalRing.ResidueField 𝒪)
    (α : Fin t → IsLocalRing.ResidueField 𝒪) (hc : OpComm N r qv S 𝒪 H) :
    Module (heckeData N r qv S 𝒪 H θ α hc).FreeAlg (Carrier N r qv 𝒪 H) :=
  (heckeData N r qv S 𝒪 H θ α hc).moduleFreeAlg

variable [NeZero N] [NeZero r] [∀ i, NeZero (qv i)] [IsLocalRing 𝒪]

end Ops

end CuspForm.TWLevel

end
