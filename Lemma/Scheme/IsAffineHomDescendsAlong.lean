import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma compactSpace_of_surjective_of_isAffine
  {P Y : (Scheme : Type (u + 1))}
  (p : P ⟶ Y) [IsAffine P] [Surjective p] :
  -- imply
  CompactSpace Y := by
  -- proof
  refine ⟨?_⟩
  rw [← p.surjective.range_eq]
  apply isCompact_range p.continuous

private lemma quasiSeparatedSpace_of_surjective_of_isAffineHom
  {P Y : (Scheme : Type (u + 1))}
  (p : P ⟶ Y) [IsAffine P] [IsAffineHom p] [Surjective p] :
  -- imply
  QuasiSeparatedSpace Y := by
  -- proof
  rw [quasiSeparatedSpace_iff_forall_affineOpens]
  intro U V
  let U' := (TopologicalSpace.Opens.map p.base).obj (U : Y.Opens)
  let V' := (TopologicalSpace.Opens.map p.base).obj (V : Y.Opens)
  have hU : IsAffineOpen U' := U.2.preimage p
  have hV : IsAffineOpen V' := V.2.preimage p
  have hc : IsCompact ((U' : Set P) ∩ (V' : Set P)) :=
    QuasiSeparatedSpace.inter_isCompact _ _ U'.2 hU.isCompact V'.2 hV.isCompact
  have himg : p.base '' ((U' : Set P) ∩ (V' : Set P)) = (U : Set Y) ∩ (V : Set Y) := by
    change p.base '' (p.base ⁻¹' (U : Set Y) ∩ p.base ⁻¹' (V : Set Y)) = _
    rw [← Set.preimage_inter, Set.image_preimage_eq _ p.surjective]
  rw [← himg]
  apply hc.image p.continuous

private lemma isPullback_specMap_appTop
  {R S : (CommRingCat : Type (u + 1))}
  {Y P : (Scheme : Type (u + 1))}
  (φ : R ⟶ S) [Flat (Spec.map φ)]
  (g : Y ⟶ Spec R) [CompactSpace Y] [QuasiSeparatedSpace Y]
  (p₁ : P ⟶ Spec S)
  (p₂ : P ⟶ Y)
  -- given
  (H : IsPullback p₁ p₂ (Spec.map φ) g) :
  -- imply
  IsPullback (Spec.map p₁.appTop) (Spec.map p₂.appTop) (Spec.map (Spec.map φ).appTop)
    (Spec.map g.appTop) := by
  -- proof
  have hUST : (⊤ : (Spec S).Opens) ≤ (TopologicalSpace.Opens.map (Spec.map φ).base).obj (⊤ : (Spec R).Opens) :=
    le_rfl
  have hUSX : (⊤ : Y.Opens) ≤ (TopologicalSpace.Opens.map g.base).obj (⊤ : (Spec R).Opens) := le_rfl
  have hUY : (⊤ : P.Opens) = (TopologicalSpace.Opens.map p₂.base).obj (⊤ : Y.Opens) ⊓
    (TopologicalSpace.Opens.map p₁.base).obj (⊤ : (Spec S).Opens) := by
    simp
  have hiso := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H.flip hUST hUSX hUY
    (isAffineOpen_top (Spec R)) (isAffineOpen_top (Spec S)) isCompact_univ isQuasiSeparated_univ
  have hpo := (isIso_pushoutSection_iff H.flip hUST hUSX hUY).mp hiso
  have := hpo.op.map Scheme.Spec
  convert this using 2
  all_goals try rfl
  all_goals simp [Scheme.Hom.appLE, Scheme.Hom.appTop, Spec.map]

private lemma isAffine_of_isPullback
  {R S : (CommRingCat : Type (u + 1))}
  {Y P : (Scheme : Type (u + 1))}
  (φ : R ⟶ S) [Surjective (Spec.map φ)] [Flat (Spec.map φ)]
  (g : Y ⟶ Spec R)
  (p₁ : P ⟶ Spec S)
  (p₂ : P ⟶ Y) [IsAffine P]
  -- given
  (H : IsPullback p₁ p₂ (Spec.map φ) g) :
  -- imply
  IsAffine Y := by
  -- proof
  have hp₂a : IsAffineHom p₂ := MorphismProperty.of_isPullback (P := @IsAffineHom) H inferInstance
  have hp₂s : Surjective p₂ := MorphismProperty.of_isPullback (P := @Surjective) H inferInstance
  have : CompactSpace Y := compactSpace_of_surjective_of_isAffine p₂
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_surjective_of_isAffineHom p₂
  have SQ1 := isPullback_specMap_appTop φ g p₁ p₂ H
  have SQiso : IsPullback (Spec S).toSpecΓ (Spec.map φ) (Spec.map (Spec.map φ).appTop) (Spec R).toSpecΓ :=
    IsPullback.of_horiz_isIso ⟨(Scheme.toSpecΓ_naturality (Spec.map φ)).symm⟩
  have s := H.paste_horiz SQiso
  rw [Scheme.toSpecΓ_naturality p₁, Scheme.toSpecΓ_naturality g] at s
  have SQ2 : IsPullback P.toSpecΓ p₂ (Spec.map p₂.appTop) Y.toSpecΓ :=
    s.of_right (Scheme.toSpecΓ_naturality p₂).symm SQ1
  have e : Spec.map (Spec.map φ).appTop = inv (Spec S).toSpecΓ ≫ Spec.map φ ≫ (Spec R).toSpecΓ := by
    rw [IsIso.eq_inv_comp, ← Scheme.toSpecΓ_naturality]
  have h1 : Surjective (Spec.map (Spec.map φ).appTop) := by
    rw [e]
    infer_instance
  have h2 : Flat (Spec.map (Spec.map φ).appTop) := by
    rw [e]
    infer_instance
  have hcov : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty (Scheme : Type (u + 1)))
    (Spec.map p₂.appTop) :=
    ⟨⟨MorphismProperty.of_isPullback (P := @Surjective) SQ1 h1,
      MorphismProperty.of_isPullback (P := @Flat) SQ1 h2⟩, inferInstance⟩
  have hiso : (isomorphisms (Scheme : Type (u + 1))) P.toSpecΓ := (isomorphisms.iff _).mpr inferInstance
  have : IsIso Y.toSpecΓ := (isomorphisms.iff _).mp
    (MorphismProperty.of_isPullback_of_descendsAlong (P := isomorphisms (Scheme : Type (u + 1)))
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) SQ2 hcov hiso)
  refine ⟨this⟩

private lemma isAffineHom_descendsAlong :
  -- imply
  DescendsAlong (@IsAffineHom : MorphismProperty (Scheme : Type (u + 1)))
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  -- proof
  apply IsZariskiLocalAtTarget.descendsAlong_inf_quasiCompact @IsAffineHom (@Surjective ⊓ @Flat)
  ·
    intro X Y f hf
    refine ⟨hf.2, (MorphismProperty.le_def (P := @IsLocalIso) (Q := @Flat)).mp (IsLocalIso.le_of_isZariskiLocalAtSource @Flat) f hf.1⟩
  ·
    intro R S Y φ g hφ h
    let _ : Surjective (Spec.map φ) := hφ.1
    let _ : Flat (Spec.map φ) := hφ.2
    let _ : IsAffineHom (pullback.fst (Spec.map φ) g) := h
    let _ : IsAffine (pullback (Spec.map φ) g) := isAffine_of_isAffineHom (pullback.fst (Spec.map φ) g)
    let _ : IsAffine Y := isAffine_of_isPullback φ g (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
    infer_instance

/--
[AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_IsAffineHom_descendsAlong_surjective_inf_flat_inf_quasiCompact.lean)
-/
@[path]
private lemma main :
  -- imply
  DescendsAlong (@IsAffineHom : MorphismProperty (Scheme : Type (u + 1)))
    (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  -- proof
  apply isAffineHom_descendsAlong


-- created on 2026-10-20
