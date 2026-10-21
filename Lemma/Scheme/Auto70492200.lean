import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_ringEquiv_sections_pullback_tensor_of_isAffineHom_of_isAffineOpen.lean)
-/
@[path]
private lemma main
  {X Y Z : (Scheme : Type (u + 1))} (a : X ⟶ Z) (b : Y ⟶ Z) [IsAffineHom a] [IsAffineHom b]
  (U : Z.Opens) (hU : IsAffineOpen U)
  (hle₂ : ((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U))) ≤ ((TopologicalSpace.Opens.map (pullback.snd a b).base).obj (((TopologicalSpace.Opens.map b.base).obj U)))) :
  let _ : Algebra (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) := (a.app U).hom.toAlgebra
  let _ : Algebra (Z.presheaf.obj (op U)) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U))) := (b.app U).hom.toAlgebra
  IsAffineOpen (((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) ∧ ∃ τ : ((pullback a b).presheaf.obj (op ((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U))))) ≃+* (TensorProduct (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U)))), (∀ s : (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))), τ (((pullback.fst a b).app (((TopologicalSpace.Opens.map a.base).obj U))).hom s) = (TensorProduct.tmul (Z.presheaf.obj (op U)) s 1)) ∧ (∀ s' : (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U))), τ (((pullback.snd a b).appLE (((TopologicalSpace.Opens.map b.base).obj U)) (((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) hle₂).hom s') = (TensorProduct.tmul (Z.presheaf.obj (op U)) 1 s')) := by
  have hUX : IsAffineOpen (((TopologicalSpace.Opens.map a.base).obj U)) := hU.preimage a
  have hUT : IsAffineOpen (((TopologicalSpace.Opens.map b.base).obj U)) := hU.preimage b
  let _ : IsAffineHom (pullback.fst a b) := MorphismProperty.pullback_fst _ _ inferInstance
  have hW : IsAffineOpen (((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) := hUX.preimage _
  refine ⟨hW, ?_⟩
  have hsq := Scheme.Hom.isPullback_resLE (IsPullback.of_hasPullback a b) (US := U) (UT := ((TopologicalSpace.Opens.map b.base).obj U))
    (UX := ((TopologicalSpace.Opens.map a.base).obj U)) le_rfl le_rfl (UY := ((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) (inf_eq_left.mpr hle₂).symm
  let _ : IsAffine (((TopologicalSpace.Opens.map a.base).obj U)) := hUX
  let _ : IsAffine (((TopologicalSpace.Opens.map b.base).obj U)) := hUT
  let _ : IsAffine U := hU
  have hpo := isPushout_appTop_of_isPullback hsq
  have key : ∀ {S T : (Scheme : Type (u + 1))} (φ : S ⟶ T) (O : T.Opens) (V : S.Opens) (e : V ≤ ((TopologicalSpace.Opens.map φ.base).obj O)), (φ.resLE O V e).appTop ≫ V.topIso.hom = O.topIso.hom ≫ φ.appLE O V e := by
    intro S T φ O V e
    change (φ.resLE O V e).app ⊤ ≫ V.topIso.hom = _
    rw [Scheme.Hom.resLE_app_top]
    ext x
    change V.topIso.hom.hom (V.topIso.inv.hom ((φ.appLE O V e).hom (O.topIso.hom.hom x))) = (φ.appLE O V e).hom (O.topIso.hom.hom x)
    apply CategoryTheory.Iso.inv_hom_id_apply V.topIso
  have hpo2 : IsPushout (a.app U) (b.app U) ((pullback.fst a b).app (((TopologicalSpace.Opens.map a.base).obj U))) ((pullback.snd a b).appLE (((TopologicalSpace.Opens.map b.base).obj U)) (((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) hle₂) := by
    refine hpo.of_iso (Scheme.Opens.topIso U) (Scheme.Opens.topIso ((TopologicalSpace.Opens.map a.base).obj U)) (Scheme.Opens.topIso ((TopologicalSpace.Opens.map b.base).obj U)) (Scheme.Opens.topIso ((TopologicalSpace.Opens.map (pullback.fst a b).base).obj ((TopologicalSpace.Opens.map a.base).obj U)))
      ?_ ?_ ?_ ?_
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key, Scheme.Hom.app_eq_appLE]
    · rw [key]
  let _ : Algebra (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) := (a.app U).hom.toAlgebra
  let _ : Algebra (Z.presheaf.obj (op U)) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U))) := (b.app U).hom.toAlgebra
  have h3 : IsPushout (a.app U) (b.app U) (CommRingCat.ofHom (Algebra.TensorProduct.includeLeftRingHom : (RingHom (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) (TensorProduct (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U))))))) (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : (AlgHom (Z.presheaf.obj (op U)) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U))) (TensorProduct (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U)))))).toRingHom) :=
    CommRingCat.isPushout_tensorProduct (Z.presheaf.obj (op U)) (X.presheaf.obj (op ((TopologicalSpace.Opens.map a.base).obj U))) (Y.presheaf.obj (op ((TopologicalSpace.Opens.map b.base).obj U)))
  let e := IsPushout.isoIsPushout _ _ hpo2 h3
  refine ⟨e.commRingCatIsoToRingEquiv, ?_, ?_⟩
  ·
    intro s
    change (((pullback.fst a b).app (((TopologicalSpace.Opens.map a.base).obj U))) ≫ e.hom).hom s = (TensorProduct.tmul (Z.presheaf.obj (op U)) s 1)
    rw [IsPushout.inl_isoIsPushout_hom]
    rfl
  ·
    intro s'
    change (((pullback.snd a b).appLE (((TopologicalSpace.Opens.map b.base).obj U)) (((TopologicalSpace.Opens.map (pullback.fst a b).base).obj (((TopologicalSpace.Opens.map a.base).obj U)))) hle₂) ≫ e.hom).hom s' = (TensorProduct.tmul (Z.presheaf.obj (op U)) 1 s')
    rw [IsPushout.inr_isoIsPushout_hom]
    rfl


-- created on 2026-10-20
