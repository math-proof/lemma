import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

/--
[AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_Hom_isIso_of_isIso_app_of_iSup_eq_top.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} {M N : X.Modules} (φ : M ⟶ N) {ι : Type v} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
  (h : ∀ (i : ι) (V : X.Opens), V ≤ U i → IsIso (φ.app V)) :
  -- imply
  IsIso φ := by
  -- proof
  have cover : ∀ x : X, ∃ i, x ∈ U i := fun x => by
    apply TopologicalSpace.Opens.mem_iSup.mp
    rw [hU]
    trivial
  let F : Sheaf (Opens.grothendieckTopology X) (AddCommGrpCat : Type (u + 1)) := ⟨M.presheaf, M.isSheaf⟩
  let G : Sheaf (Opens.grothendieckTopology X) (AddCommGrpCat : Type (u + 1)) := ⟨N.presheaf, N.isSheaf⟩
  let ψ : F ⟶ G := ⟨φ.mapPresheaf⟩
  let _ : (Opens.grothendieckTopology X).HasSheafCompose (forget (AddCommGrpCat : Type (u + 1))) := inferInstance
  have hψ : IsIso ψ := by
    refine (Sheaf.isLocallyBijective_iff_isIso ψ).mp ⟨?_, ?_⟩
    ·
      refine ⟨fun {W} x y hxy p hp => ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W.unop ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have : IsIso (φ.app (W.unop ⊓ U i)) := h i (W.unop ⊓ U i) inf_le_right
      apply (ConcreteCategory.bijective_of_isIso (φ.app (W.unop ⊓ U i))).1
      change φ.mapPresheaf.app _ (M.presheaf.map _ x) = φ.mapPresheaf.app _ (M.presheaf.map _ y)
      rw [NatTrans.naturality_apply, NatTrans.naturality_apply]
      apply congrArg _ hxy
    ·
      refine ⟨fun {W} s p hp => ?_⟩
      obtain ⟨i, hi⟩ := cover p
      refine ⟨W ⊓ U i, homOfLE inf_le_left, ?_, hp, hi⟩
      have : IsIso (φ.app (W ⊓ U i)) := h i (W ⊓ U i) inf_le_right
      obtain ⟨t, ht⟩ := (ConcreteCategory.bijective_of_isIso (φ.app (W ⊓ U i))).2 (N.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op s)
      refine ⟨t, ht⟩
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro V
  have : IsIso ((sheafToPresheaf _ _).map ψ) := inferInstance
  change IsIso (ψ.hom.app (Opposite.op V))
  change IsIso (((sheafToPresheaf _ _).map ψ).app (Opposite.op V))
  infer_instance


-- created on 2026-10-20
