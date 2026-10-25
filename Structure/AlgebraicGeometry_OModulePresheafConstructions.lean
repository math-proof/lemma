import Mathlib

import Structure.AlgebraicGeometry_OModulePresheafHom
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Instance.AlgebraicGeometry_OModulePresheafConstructions

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

variable {R : Type u} [CommRing R] {V : Scheme.{u}}

namespace Scheme.OrderedAffineCover


end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {π : V ⟶ Spec (.of R)}


variable (π) in


section KerImCoker

variable {F G : OModulePresheaf π} (φ : Hom F G)


end KerImCoker

section Pushforward

variable {Z : Scheme.{u}} (i : Z ⟶ V)

theorem appLE_algebraMap (U : V.Opens) (r : R) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ π) (i ⁻¹ᵁ U)
    (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom (algebraMap R Γ(V, U) r) = algebraMap R Γ(Z, i ⁻¹ᵁ U) r := by
  show (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom ((π.appLE ⊤ U le_top).hom _) = ((i ≫ π).appLE ⊤ (i ⁻¹ᵁ U) le_top).hom _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE]

variable (π) in

def pushforward (H : OModulePresheaf (i ≫ π)) : OModulePresheaf π where
  obj U := H.obj (i ⁻¹ᵁ U)
  module U := inferInstance
  moduleSections U := Module.compHom _ (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
  isScalarTower U := by
    letI := Scheme.TwoAffineOpenCover.algebraOfHom π U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom (i ≫ π) (i ⁻¹ᵁ U)
    letI : Module Γ(V, U) (H.obj (i ⁻¹ᵁ U)) := Module.compHom _ (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom
    refine ⟨fun r a x => ?_⟩
    show (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom (r • a) • x = r • ((i.appLE U (i ⁻¹ᵁ U) le_rfl).hom a • x)
    rw [Algebra.smul_def, map_mul, mul_smul, appLE_algebraMap, algebraMap_smul]
  res h := H.res ((Opens.map i.base).monotone h)
  res_smul {U U'} h a x := by
    show H.res _ ((i.appLE U' (i ⁻¹ᵁ U') le_rfl).hom a • x)
      = (i.appLE U (i ⁻¹ᵁ U) le_rfl).hom ((V.presheaf.map (homOfLE h).op).hom a) • H.res ((Opens.map i.base).monotone h) x
    rw [H.res_smul, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply (f := V.presheaf.map _),
      Scheme.Hom.appLE_map, Scheme.Hom.map_appLE]
  res_refl U := H.res_refl (i ⁻¹ᵁ U)
  res_comp h h' := H.res_comp ((Opens.map i.base).monotone h) ((Opens.map i.base).monotone h')


variable (π) in


end Pushforward

section AffHoms

variable (F : OModulePresheaf π)


end AffHoms

structure DevissageStep (F : OModulePresheaf π) (Y : Closeds V) where

  Z₀ : Closeds V
  isIntegral : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme
  Z₀_le : Z₀ ≤ Y
  Z₀_nonempty : (Z₀ : Set V).Nonempty

  H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π)
  isCoherent_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent
  isQuasicoherent_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent
  supportedIn_pushforward : (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).SupportedIn Z₀

  G₃ : OModulePresheaf π

  ses : AffSES (pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H) F G₃

  Z₁ : Closeds V
  Z₁_lt : Z₁ < Y
  isCoherent_G₃ : G₃.IsCoherent
  isQuasicoherent_G₃ : G₃.IsQuasicoherent
  supportedIn_G₃ : G₃.SupportedIn Z₁


end OModulePresheaf

end AlgebraicGeometry

end
