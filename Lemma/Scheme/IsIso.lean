import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X Y : (Scheme : Type (u + 1))} (f : Y ⟶ X) (U : X.Opens) [IsIso (morphismRestrict f U)]
private lemma isIso_app_of_le (V : X.Opens) (hV : V ≤ U) : IsIso (f.app V) := by
  obtain ⟨V₁, rfl⟩ : ∃ V₁ : U.toScheme.Opens, U.ι ''ᵁ V₁ = V :=
    ⟨(TopologicalSpace.Opens.map U.ι.base).obj V, by rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hV]⟩
  have h := morphismRestrict_app f U V₁
  have i1 : IsIso ((morphismRestrict f U).app V₁) := inferInstance
  have i2 : IsIso (Y.presheaf.map (eqToHom (image_morphismRestrict_preimage f U V₁)).op) := by
    rw [eqToHom_op]
    infer_instance
  refine @IsIso.of_isIso_fac_right _ _ _ _ _ _ _ _ i2 i1 h.symm
/--
[AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_isIso_app_of_isIso_morphismRestrict_of_bijective_presheaf_map.lean)
-/
@[path]
private lemma main
  {X Y : (Scheme : Type (u + 1))} (f : Y ⟶ X) [IsIntegral Y] (U : X.Opens) (hU : IsIso (morphismRestrict f U))
  (V : X.Opens) (hV : Function.Bijective (X.presheaf.map (homOfLE (inf_le_left : V ⊓ U ≤ V)).op)) :
  IsIso (f.app V) := by
  let _ := hU
  let i : V ⊓ U ⟶ V := homOfLE inf_le_left
  let rX : X.presheaf.obj (Opposite.op V) ⟶ X.presheaf.obj (Opposite.op (V ⊓ U)) := X.presheaf.map i.op
  let rY : Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map f.base).obj V)) ⟶ Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ U))) := Y.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op
  have hnat : rX ≫ f.app (V ⊓ U) = f.app V ≫ rY := f.naturality i.op
  let _ : IsIso (f.app (V ⊓ U)) := isIso_app_of_le f U (V ⊓ U) inf_le_right
  have hbU : Function.Bijective (f.app (V ⊓ U)).hom := ConcreteCategory.bijective_of_isIso (f.app (V ⊓ U))
  have hc : Function.Bijective ((f.app (V ⊓ U)).hom ∘ rX.hom) := hbU.comp hV
  have hpt : ∀ s, (f.app (V ⊓ U)).hom (rX.hom s) = rY.hom ((f.app V).hom s) := fun s => by
    have := congrArg (fun φ => φ.hom s) hnat
    simpa using this
  have hc' : Function.Bijective (rY.hom ∘ (f.app V).hom) := by
    have heq : (f.app (V ⊓ U)).hom ∘ rX.hom = rY.hom ∘ (f.app V).hom := funext hpt
    rw [← heq]
    apply hc
  rw [ConcreteCategory.isIso_iff_bijective]
  change Function.Bijective (f.app V).hom
  refine ⟨hc'.1.of_comp, fun t => ?_⟩
  if hne : Nonempty ↥((TopologicalSpace.Opens.map f.base).obj (V ⊓ U)) then
    have hinj : Function.Injective rY.hom :=
      map_injective_of_isIntegral Y ((TopologicalSpace.Opens.map f.base).map i) (H := hne)
    obtain ⟨s, hs⟩ := hc'.2 (rY.hom t)
    refine ⟨s, hinj hs⟩
  else
    have hempty : (((TopologicalSpace.Opens.map f.base).obj (V ⊓ U) : Y.Opens) : Set Y) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun h => hne h.to_subtype)
    have hbot : (TopologicalSpace.Opens.map f.base).obj (V ⊓ U) = ⊥ := TopologicalSpace.Opens.ext (hempty.trans TopologicalSpace.Opens.coe_bot.symm)
    let _ : Subsingleton (Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map f.base).obj (V ⊓ U)))) :=
      CommRingCat.subsingleton_of_isTerminal (Y.sheaf.isTerminalOfEqEmpty hbot)
    let _ : Subsingleton (X.presheaf.obj (Opposite.op V)) := hc.1.subsingleton
    have h1 : (1 : (Y.presheaf.obj (Opposite.op ((TopologicalSpace.Opens.map f.base).obj V)))) = 0 := by
      rw [← map_one (f.app V).hom, Subsingleton.elim (1 : (X.presheaf.obj (Opposite.op V))) 0, map_zero]
    refine ⟨0, ?_⟩
    rw [map_zero, ← mul_one t, h1, mul_zero]


-- created on 2026-10-20
