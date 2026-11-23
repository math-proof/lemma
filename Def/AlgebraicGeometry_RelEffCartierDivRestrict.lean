import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
import Def.AlgebraicGeometry_RelEffCartierDivSupportedIn
import Instance.AlgebraicGeometry_RelEffCartierDivRestrict

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)

noncomputable def resProdMap : pullback (f.resLE V U hUV) gV ⟶ pullback f g :=
  pullback.map _ _ _ _ U.ι (𝟙 T) V.ι (Scheme.Hom.resLE_comp_ι f hUV) (by rw [Category.id_comp, hg])

end ResProd

end Scheme.RelEffCartierDiv

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)


variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)

section Restrict

variable (hg : gV ≫ V.ι = g) (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U)

include hD in

noncomputable def restrictAlong : RelEffCartierDiv (f.resLE V U hUV) r gV :=
  haveI := isIso_pullback_snd_resProdMap f r V U hUV gV g hg D hD
  have key : (D.I.comap (resProdMap f V U hUV gV g hg)).subschemeι ≫
      pullback.snd (f.resLE V U hUV) gV =
      ((D.I.comapIso (resProdMap f V U hUV gV g hg)).hom ≫
        pullback.snd (resProdMap f V U hUV gV g hg) D.I.subschemeι) ≫
        (D.I.subschemeι ≫ pullback.snd f g) := by
    rw [← resProdMap_snd f V U hUV gV g hg, ← Scheme.IdealSheafData.comapIso_hom_fst]
    simp only [Category.assoc, pullback.condition_assoc]
  { I := D.I.comap (resProdMap f V U hUV gV g hg)
    isFinite := by have := D.isFinite; rw [key]; infer_instance
    flat := by have := D.flat; rw [key]; infer_instance
    locallyOfFinitePresentation := by have := D.locallyOfFinitePresentation; rw [key]; infer_instance
    finrank_eq := fun t => by
      have := D.isFinite; have := D.flat
      rw [key, Scheme.Hom.finrank_comp_left_of_isIso]; exact D.finrank_eq t }

end Restrict

section Extend

variable (hg : gV ≫ V.ι = g) (D' : RelEffCartierDiv (f.resLE V U hUV) r gV)

variable [IsSeparated f]

noncomputable def extendAlong : RelEffCartierDiv f r g :=
  let h := D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg
  have key : h.ker.subschemeι ≫ pullback.snd f g =
      inv h.toImage ≫ (D'.I.subschemeι ≫ pullback.snd (f.resLE V U hUV) gV) := by
    rw [IsIso.eq_inv_comp, ← Category.assoc, Scheme.Hom.toImage_imageι, Category.assoc,
      resProdMap_snd]
  { I := h.ker
    isFinite := by have := D'.isFinite; rw [key]; infer_instance
    flat := by have := D'.flat; rw [key]; infer_instance
    locallyOfFinitePresentation := by have := D'.locallyOfFinitePresentation; rw [key]; infer_instance
    finrank_eq := fun t => by
      have := D'.isFinite; have := D'.flat
      rw [key, Scheme.Hom.finrank_comp_left_of_isIso]; exact D'.finrank_eq t }

end Extend

end Scheme.RelEffCartierDiv

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
  {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)


section Range

include hUV in

end Range

end Scheme.RelEffCartierDiv
