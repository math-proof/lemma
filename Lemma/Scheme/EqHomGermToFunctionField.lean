import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false


universe u

private lemma comp_algebraMap_stalk_eq
  {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
  (φ : X.functionField →+* Y.functionField) (y : Y)
-- given
  (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
    Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) :
-- imply
    φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField) =
      (algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom  := by
-- proof
  have eX : CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField)) =
      X.presheaf.stalkSpecializes (genericPoint_specializes (π y)) ≫ CommRingCat.ofHom φ := rfl
  have eY : CommRingCat.ofHom ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom) =
      π.stalkMap y ≫ Y.presheaf.stalkSpecializes (genericPoint_specializes y) := rfl
  have key : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) =
      Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) := by
    have l1 : Spec.map (CommRingCat.ofHom (φ.comp (algebraMap (X.presheaf.stalk (π y)) X.functionField))) ≫
      X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eX, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
      apply hφπ.symm
    have l2 : Spec.map (CommRingCat.ofHom
        ((algebraMap (Y.presheaf.stalk y) Y.functionField).comp (π.stalkMap y).hom)) ≫
        X.fromSpecStalk (π y) = Y.fromSpecStalk (genericPoint Y) ≫ π := by
      rw [eY, Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
        Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
    rw [← cancel_mono (X.fromSpecStalk (π y)), l1, l2]
  refine congrArg CommRingCat.Hom.hom (Spec.map_injective key)

/--
[AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_germToFunctionField_app_eq_of_fromSpecStalk_comp_eq.lean)
-/
@[path]
private lemma main
  {X Y : Scheme} [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X)
  (φ : X.functionField →+* Y.functionField)
  {U : X.Opens} [Nonempty (U : Scheme)] [Nonempty (((TopologicalSpace.Opens.map π.base).obj U : Y.Opens) : Scheme)] (s : X.presheaf.obj (Opposite.op U))
-- given
  (hφπ : Y.fromSpecStalk (genericPoint Y) ≫ π =
    Spec.map (CommRingCat.ofHom φ) ≫ X.fromSpecStalk (genericPoint X)) :
-- imply
    (Y.germToFunctionField ((TopologicalSpace.Opens.map π.base).obj U)).hom (π.app U s) = φ ((X.germToFunctionField U).hom s)  := by
-- proof
  have hη : genericPoint Y ∈ (TopologicalSpace.Opens.map π.base).obj U :=
    ((genericPoint_spec Y).mem_open_set_iff ((TopologicalSpace.Opens.map π.base).obj U).isOpen).mpr (by simpa using ‹Nonempty (((TopologicalSpace.Opens.map π.base).obj U : Y.Opens) : Scheme)›)
  have hπη : π (genericPoint Y) ∈ U := hη
  have hc := comp_algebraMap_stalk_eq π φ (genericPoint Y) hφπ
  have hc' : φ.comp (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y)))).hom =
      (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom.comp
        (π.stalkMap (genericPoint Y)).hom := hc
  have e1 : X.germToFunctionField U =
      X.presheaf.germ U (π (genericPoint Y)) hπη ≫
        X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y))) :=
    (X.presheaf.germ_stalkSpecializes hπη (genericPoint_specializes _)).symm
  have e2 : (Y.presheaf.stalkSpecializes (genericPoint_specializes (genericPoint Y))).hom = RingHom.id _ := by
    rw [Y.presheaf.stalkSpecializes_refl]; rfl
  have e3 : (π.stalkMap (genericPoint Y)).hom ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) =
      (Y.presheaf.germ ((TopologicalSpace.Opens.map π.base).obj U) (genericPoint Y) hπη).hom (π.app U s) := by
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.germ_stalkMap]
  have e1' : (X.germToFunctionField U).hom s =
      (X.presheaf.stalkSpecializes (genericPoint_specializes (π (genericPoint Y)))).hom
        ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s) := by
    rw [e1]; rfl
  have hcs := congrArg (fun g => g ((X.presheaf.germ U (π (genericPoint Y)) hπη).hom s)) hc'
  simp only [RingHom.comp_apply, e2, RingHom.id_apply, e3] at hcs
  rw [e1', hcs]


-- created on 2026-10-20
