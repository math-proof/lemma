import Mathlib
import Def.AlgebraicCurve_PlacesOf
import Lemma.AlgebraicGeometry.TwoAffineOpenCoverKaehler

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

namespace AlgebraicCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (c : X ⟶ Spec (.of k)) [IsIntegral X]

theorem germToFunctionField_algebraMap (U : X.Opens) [Nonempty U] (r : k) :
    (X.germToFunctionField U).hom ((Scheme.TwoAffineOpenCover.algebraOfHom c U).algebraMap r)
      = baseToFunctionField c r := by
  rw [Scheme.TwoAffineOpenCover.algebraMap_algebraOfHom]
  simp only [baseToFunctionField, RingHom.coe_comp, Function.comp_apply]
  change (c.appLE ⊤ U le_top ≫ X.germToFunctionField U).hom _
    = (c.appTop ≫ X.presheaf.germ ⊤ (genericPoint X) trivial).hom _
  congr 2
  rw [Scheme.Hom.appLE, Category.assoc]
  erw [TopCat.Presheaf.germ_res]
  try rfl

theorem germToFunctionField_comp_algebraMap (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    (X.germToFunctionField U).hom.comp (algebraMap k Γ(X, U))
      = (algebraMap k X.functionField).comp (RingHom.id k) :=
  RingHom.ext fun r => germToFunctionField_algebraMap c U r

omit [IsIntegral X] in

theorem germToFunctionField_map [IrreducibleSpace X] {U V : X.Opens} [Nonempty U] [Nonempty V]
    (h : V ≤ U) (s : Γ(X, U)) :
    (X.germToFunctionField V).hom ((X.presheaf.map (homOfLE h).op).hom s)
      = (X.germToFunctionField U).hom s := by
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  erw [TopCat.Presheaf.germ_res]
  try rfl

def kaehlerToFunctionField (U : X.Opens) [Nonempty U] :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    Ω[Γ(X, U)⁄k] →ₗ[k] Ω[X.functionField⁄k] :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom (RingHom.id k) (X.germToFunctionField U).hom
    (germToFunctionField_comp_algebraMap c U)

variable (U : X.Opens) [Nonempty U]

theorem kaehlerToFunctionField_D (s : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (KaehlerDifferential.D k Γ(X, U) s)
      = KaehlerDifferential.D k X.functionField ((X.germToFunctionField U).hom s) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_D _ _ _ s

theorem kaehlerToFunctionField_smul (a : Γ(X, U))
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k]) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (a • η) = (X.germToFunctionField U).hom a • kaehlerToFunctionField c U η :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_smul _ _ _ a η

theorem kaehlerToFunctionField_smul_D (a s : Γ(X, U)) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := (baseToFunctionField c).toAlgebra
    kaehlerToFunctionField c U (a • KaehlerDifferential.D k Γ(X, U) s)
      = (X.germToFunctionField U).hom a • KaehlerDifferential.D k X.functionField ((X.germToFunctionField U).hom s) :=
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := (baseToFunctionField c).toAlgebra
  KaehlerDifferential.mapOfRingHom_smul_D _ _ _ a s

theorem kaehlerToFunctionField_map {U V : X.Opens} [Nonempty U] [Nonempty V] (h : V ≤ U)
    (η : letI := Scheme.TwoAffineOpenCover.algebraOfHom c U; Ω[Γ(X, U)⁄k]) :
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
    letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
    kaehlerToFunctionField c V
        (KaehlerDifferential.mapOfRingHom (RingHom.id k) (Scheme.TwoAffineOpenCover.restrictAlgHom c h).toRingHom
          (RingHom.ext fun r => (Scheme.TwoAffineOpenCover.restrictAlgHom c h).commutes r) η)
      = kaehlerToFunctionField c U η := by
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c U
  letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
  letI := (baseToFunctionField c).toAlgebra
  have hcomp : (X.germToFunctionField V).hom.comp (Scheme.TwoAffineOpenCover.restrictAlgHom c h).toRingHom
      = (X.germToFunctionField U).hom :=
    RingHom.ext fun s => germToFunctionField_map (X := X) h s
  unfold kaehlerToFunctionField
  rw [KaehlerDifferential.mapOfRingHom_comp_apply _ _ _ _ _ _
    (h₃ := by rw [hcomp]; exact germToFunctionField_comp_algebraMap c U)]
  exact KaehlerDifferential.mapOfRingHom_congr hcomp _ _ η

end AlgebraicCurve

namespace AlgebraicGeometry.Scheme.TwoAffineOpenCover

open AlgebraicCurve

variable {k : Type u} [Field k] {X : Scheme.{u}} (𝒱 : X.TwoAffineOpenCover) (c : X ⟶ Spec (.of k))
  [IsIntegral X] [Nonempty 𝒱.U0] [Nonempty 𝒱.U1] [Nonempty (𝒱.U0 ⊓ 𝒱.U1 : X.Opens)]

omit [Nonempty 𝒱.U1] in

theorem kaehlerToFunctionField_r0 (ω : Ω[(𝒱.cover c).A0⁄k]) :
    kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r0 ω) = kaehlerToFunctionField c 𝒱.U0 ω :=
  kaehlerToFunctionField_map c inf_le_left ω

omit [Nonempty 𝒱.U0] in

theorem kaehlerToFunctionField_r1 (ω : Ω[(𝒱.cover c).A1⁄k]) :
    kaehlerToFunctionField c (𝒱.U0 ⊓ 𝒱.U1) ((𝒱.kaehlerSections c).r1 ω) = kaehlerToFunctionField c 𝒱.U1 ω :=
  kaehlerToFunctionField_map c inf_le_right ω

theorem kaehlerToFunctionField_fst_eq_snd_of_mem_H0 (ω : (𝒱.kaehlerSections c).H0) :
    kaehlerToFunctionField c 𝒱.U0 ω.val.1 = kaehlerToFunctionField c 𝒱.U1 ω.val.2 := by
  rw [← kaehlerToFunctionField_r0, ← kaehlerToFunctionField_r1]
  have h := (TwoChartCech.Sections.mem_H0_iff _ _).mp ω.2
  exact congrArg _ h

end AlgebraicGeometry.Scheme.TwoAffineOpenCover

end
