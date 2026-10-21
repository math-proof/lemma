import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false


private lemma eq_of_comp_eq_of_surjective
  {X Y T T₀ : (Scheme : Type 1)}
  (q : Y ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
  (k : T₀ ⟶ T) [Surjective k]
  {s₁ s₂ : T ⟶ Y}
  -- given
  (hq : s₁ ≫ q = s₂ ≫ q)
  (hk : k ≫ s₁ = k ≫ s₂) :
  -- imply
  s₁ = s₂ := by
  -- proof
  let _ : IsOpenImmersion (pullback.diagonal q) := inferInstance
  let _ : IsOpenImmersion (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := inferInstance
  have hfac : k ≫ pullback.lift s₁ s₂ hq = (k ≫ s₁) ≫ pullback.diagonal q := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
    · simp only [Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id, hk]
  have hk' : pullback.lift k (k ≫ s₁) hfac ≫ pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q) = k :=
    pullback.lift_fst _ _ _
  let _ : Surjective (pullback.lift k (k ≫ s₁) hfac ≫
    pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) := by
    rw [hk']
    infer_instance
  let _ : Surjective (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    Surjective.of_comp (pullback.lift k (k ≫ s₁) hfac) _
  let _ : IsIso (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) :=
    (isIso_iff_isOpenImmersion_and_surjective _).mpr ⟨inferInstance, inferInstance⟩
  have hp : pullback.lift s₁ s₂ hq =
    inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
    pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q := by
    rw [← pullback.condition, IsIso.inv_hom_id_assoc]
  have h1 : s₁ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
    pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := calc
    _ = pullback.lift s₁ s₂ hq ≫ pullback.fst q q := (pullback.lift_fst _ _ _).symm
    _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
      pullback.fst q q := by
      rw [← hp]
    _ = _ := by
      simp only [Category.assoc, pullback.diagonal_fst, Category.comp_id]
  have h2 : s₂ = inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
    pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) := calc
    _ = pullback.lift s₁ s₂ hq ≫ pullback.snd q q := (pullback.lift_snd _ _ _).symm
    _ = (inv (pullback.fst (pullback.lift s₁ s₂ hq) (pullback.diagonal q)) ≫
      pullback.snd (pullback.lift s₁ s₂ hq) (pullback.diagonal q) ≫ pullback.diagonal q) ≫
      pullback.snd q q := by
      rw [← hp]
    _ = _ := by
      simp only [Category.assoc, pullback.diagonal_snd, Category.comp_id]
  rw [h1, ← h2]

private lemma surjective_of_isNilpotent_ker
  {T T₀ : (Scheme : Type 1)}
  (k : T₀ ⟶ T) [IsClosedImmersion k]
  -- given
  (hk : IsNilpotent k.ker) :
  -- imply
  Surjective k := by
  -- proof
  have : IsDominant k := by
    obtain ⟨n, hn⟩ := hk
    rw [isDominant_iff, denseRange_iff_closure_range, ← k.support_ker,
      ← k.ker.support_pow (n + 1) (by simp), pow_succ, hn]
    simp
  refine ⟨by rw [← Set.range_eq_univ, ← k.isClosedEmbedding.isClosed_range.closure_eq, k.denseRange.closure_range]⟩

private lemma exists_of_forall_exists_nhd
  {X Y T T₀ : (Scheme : Type 1)}
  (q : Y ⟶ X) [FormallyUnramified q] [LocallyOfFiniteType q]
  (k : T₀ ⟶ T) [Surjective k]
  (t : T ⟶ X)
  (s₀ : T₀ ⟶ Y)
  -- given
  (hs₀ : s₀ ≫ q = k ≫ t)
  (H : ∀ p : T, ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : (Scheme : Type 1)) ⟶ Y), sU ≫ q = U.ι ≫ t ∧ morphismRestrict k U ≫ sU = Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj U) ≫ s₀) :
  -- imply
  ∃ s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  -- proof
  choose U hpU sU hsUq hsUk using H
  let 𝒰 : T.OpenCover :=
    { I₀ := T
      X := fun i => (U i)
      f := fun i => (U i).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x => ⟨x, by simpa using hpU x⟩, inferInstance⟩ }
  have hcompat : ∀ i j : T, pullback.fst (𝒰.f i) (𝒰.f j) ≫ sU i = pullback.snd (𝒰.f i) (𝒰.f j) ≫ sU j := by
    intro i j
    let g : pullback (𝒰.f i) (𝒰.f j) ⟶ T := pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι
    have hg : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι = g := (pullback.condition).symm
    have key : ∀ (l : T) (m : pullback (𝒰.f i) (𝒰.f j) ⟶ (U l : (Scheme : Type 1))) (hm : m ≫ (U l).ι = g), pullback.snd k g ≫ m ≫ sU l = pullback.fst k g ≫ s₀ := by
      intro l m hm
      have w : (pullback.snd k g ≫ m) ≫ (U l).ι = pullback.fst k g ≫ k := by
        rw [Category.assoc, hm, pullback.condition]
      let n := (isPullback_morphismRestrict k (U l)).lift (pullback.snd k g ≫ m) (pullback.fst k g) w
      have hn1 : n ≫ morphismRestrict k (U l) = pullback.snd k g ≫ m := IsPullback.lift_fst _ _ _ _
      have hn2 : n ≫ Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj (U l)) = pullback.fst k g := IsPullback.lift_snd _ _ _ _
      rw [← Category.assoc, ← hn1, Category.assoc, hsUk, ← Category.assoc, hn2]
    let _ : Surjective (pullback.snd k g) := inferInstance
    refine eq_of_comp_eq_of_surjective q (pullback.snd k g) ?_ ?_
    · rw [Category.assoc, hsUq, Category.assoc, hsUq, ← Category.assoc, ← Category.assoc, pullback.condition]
    · rw [key i (pullback.fst (𝒰.f i) (𝒰.f j)) rfl, key j (pullback.snd (𝒰.f i) (𝒰.f j)) hg]
  refine ⟨𝒰.glueMorphisms sU hcompat, ?_, ?_⟩
  · refine Scheme.Cover.hom_ext 𝒰 _ _ fun i => ?_
    rw [Scheme.Cover.ι_glueMorphisms_assoc, hsUq]
  ·
    let 𝒱 : T₀.OpenCover :=
      { I₀ := T
        X := fun i => (TopologicalSpace.Opens.map k.base).obj (U i)
        f := fun i => Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj (U i))
        mem₀ := by
          rw [Scheme.presieve₀_mem_precoverage_iff]
          refine ⟨fun x => ⟨k.base x, by simpa using hpU (k.base x)⟩, inferInstance⟩ }
    refine Scheme.Cover.hom_ext 𝒱 _ _ fun i => ?_
    show Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj (U i)) ≫ k ≫ 𝒰.glueMorphisms sU hcompat = Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj (U i)) ≫ s₀
    rw [← morphismRestrict_ι_assoc, show (U i).ι = 𝒰.f i from rfl, Scheme.Cover.ι_glueMorphisms, hsUk]

private lemma appLE_congr_hom
  {X Y : (Scheme : Type 1)}
  {f g : X ⟶ Y}
  {U : Y.Opens}
  {V : X.Opens}
  {e : V ≤ (TopologicalSpace.Opens.map f.base).obj U}
  {e' : V ≤ (TopologicalSpace.Opens.map g.base).obj U}
  -- given
  (h : f = g) :
  -- imply
  f.appLE U V e = g.appLE U V e' := by
  -- proof
  subst h
  rfl

private lemma exists_nhd_lift
  {X Y T T₀ : (Scheme : Type 1)}
  (q : Y ⟶ X) [Etale q]
  (k : T₀ ⟶ T) [IsClosedImmersion k]
  (t : T ⟶ X)
  (s₀ : T₀ ⟶ Y)
  -- given
  (hk : IsNilpotent k.ker)
  (hs₀ : s₀ ≫ q = k ≫ t)
  (p : T) :
  -- imply
  ∃ (U : T.Opens) (_ : p ∈ U) (sU : (U : (Scheme : Type 1)) ⟶ Y), sU ≫ q = U.ι ≫ t ∧ morphismRestrict k U ≫ sU = Scheme.Opens.ι ((TopologicalSpace.Opens.map k.base).obj U) ≫ s₀ := by
  -- proof
  let _ : Surjective k := surjective_of_isNilpotent_ker k hk
  obtain ⟨p₀, hp₀⟩ := k.surjective p
  obtain ⟨_, ⟨R', hR', rfl⟩, hpR', -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (t.base p)) isOpen_univ
  have hqs : q.base (s₀.base p₀) = t.base p := by
    have := congrArg (fun f : T₀ ⟶ X => f.base p₀) hs₀
    simpa [hp₀] using this
  have hy : s₀.base p₀ ∈ (TopologicalSpace.Opens.map q.base).obj R' := by
    show q.base (s₀.base p₀) ∈ R'
    rw [hqs]
    apply hpR'
  obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWR'⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open hy ((TopologicalSpace.Opens.map q.base).obj R').isOpen
  change W ≤ (TopologicalSpace.Opens.map q.base).obj R' at hWR'
  have hOopen : IsOpen ((Set.image k.base (((TopologicalSpace.Opens.map s₀.base).obj W : Set T₀)ᶜ))ᶜ) := by
    rw [isOpen_compl_iff]
    apply k.isClosedEmbedding.isClosedMap _ (isClosed_compl_iff.mpr ((TopologicalSpace.Opens.map s₀.base).obj W).isOpen)
  let O : T.Opens := ⟨(Set.image k.base (((TopologicalSpace.Opens.map s₀.base).obj W : Set T₀)ᶜ))ᶜ, hOopen⟩
  have hpO : p ∈ O := by
    rintro ⟨x, hx, hxp⟩
    apply hx
    have : x = p₀ := k.isClosedEmbedding.injective (hxp.trans hp₀.symm)
    subst this
    apply hyW
  obtain ⟨_, ⟨U, hU, rfl⟩, hpU, hUle⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
    (show p ∈ (((TopologicalSpace.Opens.map t.base).obj R' ⊓ O : T.Opens) : Set T) from ⟨hpR', hpO⟩)
    ((TopologicalSpace.Opens.map t.base).obj R' ⊓ O).isOpen
  have hUR' : U ≤ (TopologicalSpace.Opens.map t.base).obj R' := fun x hx => (hUle hx).1
  have hkUW : (TopologicalSpace.Opens.map k.base).obj U ≤ (TopologicalSpace.Opens.map s₀.base).obj W := by
    intro x hx
    by_contra hxW
    apply (hUle hx).2 ⟨x, hxW, rfl⟩
  have hkU : IsAffineOpen ((TopologicalSpace.Opens.map k.base).obj U) := hU.preimage k
  have hkUR' : (TopologicalSpace.Opens.map k.base).obj U ≤ (TopologicalSpace.Opens.map (k ≫ t).base).obj R' :=
    fun x hx => hUR' hx
  have hφ : (q.appLE R' W hWR').hom.Etale :=
    HasRingHomProperty.appLE (P := @Etale) q inferInstance ⟨R', hR'⟩ ⟨W, hW⟩ hWR'
  algebraize [(q.appLE R' W hWR').hom, (t.appLE R' U hUR').hom, ((k ≫ t).appLE R' ((TopologicalSpace.Opens.map k.base).obj U) hkUR').hom]
  let σ : AlgHom (X.presheaf.obj (op R')) (Y.presheaf.obj (op W)) (T₀.presheaf.obj (op ((TopologicalSpace.Opens.map k.base).obj U))) := ⟨(s₀.appLE W ((TopologicalSpace.Opens.map k.base).obj U) hkUW).hom, fun r => by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]
    rw [appLE_congr_hom hs₀]⟩
  let κ : AlgHom (X.presheaf.obj (op R')) (T.presheaf.obj (op U)) (T₀.presheaf.obj (op ((TopologicalSpace.Opens.map k.base).obj U))) := ⟨(k.appLE U ((TopologicalSpace.Opens.map k.base).obj U) le_rfl).hom, fun r => by
    simp only [RingHom.algebraMap_toAlgebra, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE, RingHom.toMonoidHom_eq_coe, OneHom.toFun_eq_coe, MonoidHom.toOneHom_coe, MonoidHom.coe_coe]⟩
  have hκs : Function.Surjective κ := by
    show Function.Surjective (k.appLE U ((TopologicalSpace.Opens.map k.base).obj U) le_rfl).hom
    rw [← Scheme.Hom.app_eq_appLE]
    apply k.app_surjective U hU
  have hκn : IsNilpotent (RingHom.ker (κ : RingHom (T.presheaf.obj (op U)) (T₀.presheaf.obj (op ((TopologicalSpace.Opens.map k.base).obj U))))) := by
    show IsNilpotent (RingHom.ker (k.appLE U ((TopologicalSpace.Opens.map k.base).obj U) le_rfl).hom)
    rw [← Scheme.Hom.app_eq_appLE]
    obtain ⟨n, hn⟩ := hk
    refine ⟨n, by simpa using congrArg (fun I => I.ideal ⟨U, hU⟩) hn⟩
  let ψ : AlgHom (X.presheaf.obj (op R')) (Y.presheaf.obj (op W)) (T.presheaf.obj (op U)) := Algebra.FormallySmooth.liftOfSurjective σ κ hκs hκn
  have hψ : κ.comp ψ = σ := Algebra.FormallySmooth.comp_liftOfSurjective σ κ hκs hκn
  refine ⟨U, hpU, hU.isoSpec.hom ≫ Spec.map (CommRingCat.ofHom ψ.toRingHom) ≫ hW.fromSpec, ?_, ?_⟩
  ·
    have h1 : q.appLE R' W hWR' ≫ CommRingCat.ofHom ψ.toRingHom = t.appLE R' U hUR' := by
      ext r
      change ψ (algebraMap (X.presheaf.obj (op R')) (Y.presheaf.obj (op W)) r) = algebraMap (X.presheaf.obj (op R')) (T.presheaf.obj (op U)) r
      apply ψ.commutes r
    rw [Category.assoc, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec q hR' hW hWR',
      ← Spec.map_comp_assoc, h1, IsAffineOpen.SpecMap_appLE_fromSpec t hR' hU hUR', ← hU.isoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
  ·
    have h2 : CommRingCat.ofHom ψ.toRingHom ≫ k.appLE U ((TopologicalSpace.Opens.map k.base).obj U) le_rfl = s₀.appLE W ((TopologicalSpace.Opens.map k.base).obj U) hkUW := by
      ext a
      change κ (ψ a) = σ a
      rw [← hψ]
      rfl
    have h3 : Spec.map (k.appLE U ((TopologicalSpace.Opens.map k.base).obj U) le_rfl) ≫ hU.isoSpec.inv = hkU.isoSpec.inv ≫ morphismRestrict k U := by
      rw [← cancel_mono (Scheme.Opens.ι U), Category.assoc, Category.assoc, hU.isoSpec_inv_ι, morphismRestrict_ι,
        IsAffineOpen.SpecMap_appLE_fromSpec k hU hkU le_rfl, ← hkU.isoSpec_inv_ι, Category.assoc]
    rw [← cancel_epi hkU.isoSpec.inv, ← Category.assoc, ← h3, Category.assoc, Iso.inv_hom_id_assoc,
      ← Spec.map_comp_assoc, h2, IsAffineOpen.SpecMap_appLE_fromSpec s₀ hW hkU hkUW, ← Category.assoc, hkU.isoSpec_inv_ι]

private lemma existsUnique_comp_eq_of_isNilpotent_ker
  {X Y T T₀ : (Scheme : Type 1)}
  (q : Y ⟶ X) [Etale q]
  (k : T₀ ⟶ T) [IsClosedImmersion k]
  (t : T ⟶ X)
  (s₀ : T₀ ⟶ Y)
  -- given
  (hk : IsNilpotent k.ker)
  (hs₀ : s₀ ≫ q = k ≫ t) :
  -- imply
  ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ := by
  -- proof
  let _ : Surjective k := surjective_of_isNilpotent_ker k hk
  obtain ⟨s, hs, hks⟩ := exists_of_forall_exists_nhd q k t s₀ hs₀ (exists_nhd_lift q k t s₀ hk hs₀)
  refine ⟨s, ⟨hs, hks⟩, fun s' hs' => ?_⟩
  apply eq_of_comp_eq_of_surjective q k (hs'.1.trans hs.symm) (hs'.2.trans hks.symm)

/--
[AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Etale_existsUnique_comp_eq_of_isNilpotent_ker.lean)
-/
@[path]
private lemma main
  {X Y T T₀ : (Scheme : Type 1)}
  (q : Y ⟶ X) [Etale q]
  (k : T₀ ⟶ T) [IsClosedImmersion k]
  (t : T ⟶ X)
  (s₀ : T₀ ⟶ Y)
  -- given
  (hk : IsNilpotent k.ker)
  (hs₀ : s₀ ≫ q = k ≫ t) :
  -- imply
  ∃! s : T ⟶ Y, s ≫ q = t ∧ k ≫ s = s₀ :=
  existsUnique_comp_eq_of_isNilpotent_ker q k t s₀ hk hs₀


-- created on 2026-10-20
