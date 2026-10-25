import Mathlib
import Abbrev.ModularCurve_DRModelPackage
import Def.ModularCurve_X0MqResolvedTable
import Def.AlgebraicCurve_RelCartier
import Instance.AlgebraicGeometry_RelativePicardFunctor

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

noncomputable section

namespace ModularCurve

def DRResolvedModelPackage.chainPos {node : Type} (width : node → ℕ) (n : node) (d : ℕ) : X0MqComponents width :=
  if h0 : d = 0 then Sum.inl 0
  else if h : d < width n then Sum.inr ⟨n, ⟨d - 1, by omega⟩⟩
  else Sum.inl 1

variable (p : ℕ) [Fact p.Prime]

variable {p} in

def DRModel.baseChangeMap {O κ : Type} [CommRing O] [CommRing κ] (toκ : O →+* κ) :
    pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ κ))) ⟶
      pullback (DRModel.toBase p) (Spec.map (CommRingCat.ofHom (algebraMap ℤ O))) :=
  pullback.map _ _ _ _ (𝟙 _) (Spec.map (CommRingCat.ofHom toκ)) (𝟙 _)
    (by rw [Category.comp_id, Category.id_comp])
    (by
      rw [Category.comp_id, ← Spec.map_comp]
      congr 1
      ext1
      exact RingHom.ext_int _ _)

end ModularCurve

end
