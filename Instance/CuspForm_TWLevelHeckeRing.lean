-- Carved from Lemma/Definitions/Def_CuspForm_TWLevelHeckeRing.lean: instance decls only.
import Instance.CuspForm_TWLevelHeckeModule
import Lemma.CuspForm.TWLevelHeckeRing

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups


namespace CuspForm.TWLevel

variable (N r : ℕ) {t : ℕ} (qv : Fin t → ℕ) (S : Set ℕ) (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]

instance heckeSubalgebra_isMulCommutative :
    IsMulCommutative ↥(heckeSubalgebra N r qv S 𝒪 H θ α hc hdc) :=
  Algebra.isMulCommutative_adjoin 𝒪 (heckeRingGens_comm N r qv S 𝒪 H θ α hc hdc)

instance HeckeRing.instCommRing : CommRing (HeckeRing N r qv S 𝒪 H θ α hc hdc) :=
  { (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).toRing with
    mul_comm := (heckeSubalgebra_isMulCommutative N r qv S 𝒪 H θ α hc hdc).is_comm.comm }

instance HeckeRing.instAlgebra : Algebra 𝒪 (HeckeRing N r qv S 𝒪 H θ α hc hdc) :=
  (heckeSubalgebra N r qv S 𝒪 H θ α hc hdc).algebra

instance HeckeRing.instModuleSelf :
    @Module (HeckeRing N r qv S 𝒪 H θ α hc hdc) (HeckeRing N r qv S 𝒪 H θ α hc hdc) _
      AddCommGroup.toAddCommMonoid :=
  Semiring.toModule

instance HeckeRing.instInhabited : Inhabited (HeckeRing N r qv S 𝒪 H θ α hc hdc) := ⟨0⟩


end CuspForm.TWLevel

end
