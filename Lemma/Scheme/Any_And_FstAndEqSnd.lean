import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma flat_SpecMap_of_field [Field k] [Field L] (φ : CommRingCat.of k ⟶ CommRingCat.of L) : Flat (Spec.map φ) := by
  rw [Flat.SpecMap_iff]
  let _ := φ.hom.toAlgebra
  change Module.Flat k L
  infer_instance
private lemma helper_main [CommRing R] [IsLocalRing R] {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R)) (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R) (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) : ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧ (pullback.snd f f).base θ' = y := by
  set a : X := (pullback.fst f f).base θ with ha
  set s : ↑(Spec (CommRingCat.of R)) := f.base a with hs
  let ιa : Spec (X.residueField a) ⟶ X := X.fromSpecResidueField a
  let ιs : Spec ((Spec (CommRingCat.of R)).residueField s) ⟶ Spec (CommRingCat.of R) := (Spec (CommRingCat.of R)).fromSpecResidueField s
  let r := f.residueFieldMap a
  have hr : Spec.map r ≫ ιs = ιa ≫ f := f.SpecMap_residueFieldMap_fromSpecResidueField a
  let _ : Flat (Spec.map r) := flat_SpecMap_of_field r
  let jXs : pullback ιs f ⟶ X := pullback.snd ιs f
  let E := pullback (Spec.map r) (pullback.fst ιs f)
  let g₂ : E ⟶ pullback ιs f := pullback.snd (Spec.map r) (pullback.fst ιs f)
  let _ : Flat g₂ := inferInstance
  let iso : E ≅ pullback (Spec.map r ≫ ιs) f := pullbackRightPullbackFstIso ιs f (Spec.map r)
  let ψ₀ : pullback (Spec.map r ≫ ιs) f ⟶ pullback f f := pullback.map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _) (by rw [hr, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
  let ψ : E ⟶ pullback f f := iso.hom ≫ ψ₀
  have hψsnd : ψ ≫ pullback.snd f f = g₂ ≫ jXs := by
    simp [ψ, ψ₀, Category.assoc, pullback.lift_snd, Category.comp_id]
    apply pullbackRightPullbackFstIso_hom_snd ιs f (Spec.map r)
  have hψfst : ψ ≫ pullback.fst f f = (iso.hom ≫ pullback.fst _ _) ≫ ιa := by
    simp [ψ, ψ₀, Category.assoc, pullback.lift_fst]
  have hrangeψ₀ : Set.range ψ₀.base = {q | (pullback.fst f f).base q = a} := by
    have h := Scheme.Pullback.range_map (Spec.map r ≫ ιs) f f f ιa (𝟙 X) (𝟙 _) (by rw [hr, Category.comp_id]) (by rw [Category.comp_id, Category.id_comp])
    rw [h]
    ext q
    simp [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq, ιa, Scheme.range_fromSpecResidueField, Set.mem_singleton_iff]
    constructor
    ·
      intro h
      apply h.1
    ·
      intro hq
      exact ⟨hq, ⟨(pullback.snd f f).base q, by simp⟩⟩
  have hrangeψ : Set.range ψ.base = {q | (pullback.fst f f).base q = a} := by
    rw [← hrangeψ₀]
    change Set.range ((iso.hom ≫ ψ₀).base) = _
    have : Set.range ((iso.hom ≫ ψ₀).base) = ψ₀.base '' Set.range iso.hom.base := by
      rw [← Set.range_comp]
      rfl
    rw [this, (show Function.Surjective iso.hom.base from (Scheme.homeoOfIso iso).surjective).range_eq, Set.image_univ]
  obtain ⟨θ₁, hθ₁⟩ : θ ∈ Set.range ψ.base := by
    rw [hrangeψ]
    apply ha.symm
  have hrange_jXs : Set.range jXs.base = {x | f.base x = s} := by
    change Set.range (pullback.snd ιs f).base = _
    rw [Scheme.Pullback.range_snd]
    ext x
    simp [ιs, Set.mem_preimage, Scheme.range_fromSpecResidueField, Set.mem_singleton_iff, Set.mem_ofPred_eq]
  have hys' : f.base y = s := by
    rw [hys]
    apply hθ.symm
  obtain ⟨y₁, rfl⟩ : y ∈ Set.range jXs.base := by
    rw [hrange_jXs]
    apply hys'
  have hsndθ : (pullback.snd f f).base θ = jXs.base (g₂.base θ₁) := by
    rw [← hθ₁, ← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply]
  have hy₁ : y₁ ⤳ g₂.base θ₁ := by
    rw [← jXs.isEmbedding.isInducing.specializes_iff, ← hsndθ]
    apply hy
  obtain ⟨ε, hεθ₁, hεy⟩ := Flat.generalizingMap g₂ hy₁
  refine ⟨ψ.base ε, ?_, ?_, ?_⟩
  ·
    rw [← hθ₁]
    apply hεθ₁.map ψ.continuous
  ·
    have h1 : ψ.base ε ∈ Set.range ψ.base := ⟨ε, rfl⟩
    rw [hrangeψ] at h1
    apply h1
  ·
    rw [← Scheme.Hom.comp_apply, hψsnd, Scheme.Hom.comp_apply, hεy]
/--
[NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_NeronModelInfra_exists_specializes_fst_eq_snd_eq_of_specializes_snd.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsLocalRing R]
  {X : Scheme} (f : X ⟶ Spec (CommRingCat.of R))
  (θ : ↑(pullback f f)) (hθ : f.base ((pullback.fst f f).base θ) = IsLocalRing.closedPoint R)
  (y : X) (hy : y ⤳ (pullback.snd f f).base θ) (hys : f.base y = IsLocalRing.closedPoint R) :
  -- imply
  ∃ θ' : ↑(pullback f f), θ' ⤳ θ ∧ (pullback.fst f f).base θ' = (pullback.fst f f).base θ ∧ (pullback.snd f f).base θ' = y :=
  helper_main f θ hθ y hy hys


-- created on 2026-10-20
