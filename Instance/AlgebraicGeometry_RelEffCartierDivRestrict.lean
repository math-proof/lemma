-- Carved from Lemma/Definitions/Def_AlgebraicGeometry_RelEffCartierDivRestrict.lean: instance decls only.
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Lemma.AlgebraicGeometry.RelEffCartierDivSupportedIn
import Lemma.AlgebraicGeometry.RelEffCartierDivRestrict

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)

instance isOpenImmersion_resProdMap : IsOpenImmersion (resProdMap f V U hUV gV g hg) := by
  delta resProdMap; infer_instance

end ResProd

end AlgebraicGeometry.RelEffCartierDiv

namespace AlgebraicGeometry.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)


variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)


section Extend

variable (hg : gV ≫ V.ι = g) (D' : RelEffCartierDiv (f.resLE V U hUV) r gV)

instance isClosedImmersion_subschemeι_resProdMap [IsSeparated f] :
    IsClosedImmersion (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) := by
  rw [IsClosedImmersion.iff_isFinite_and_mono]
  refine ⟨?_, inferInstance⟩
  have : IsFinite ((D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) ≫ pullback.snd f g) := by
    rw [Category.assoc, resProdMap_snd]; exact D'.isFinite
  exact MorphismProperty.of_postcomp (W := @IsFinite) (W' := @IsSeparated) _ (pullback.snd f g)
    inferInstance this

variable [IsSeparated f]

end Extend

end AlgebraicGeometry.RelEffCartierDiv

