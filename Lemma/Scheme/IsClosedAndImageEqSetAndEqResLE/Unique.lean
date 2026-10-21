import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type (u + 1))}
private lemma mem_preimage_iff {Y : (Scheme : Type (u + 1))} (f : X ⟶ Y) (W : Y.Opens) (x : X) : x ∈ ((TopologicalSpace.Opens.map f.base).obj W) ↔ f.base x ∈ W := Iff.rfl
private noncomputable def pair (A B : X.Opens) : Bool → X.Opens := fun b => cond b A B
private lemma isOpenCover_pair (A B : X.Opens) (h : A ⊔ B = ⊤) : IsOpenCover (pair A B) := by
  show ⨆ b, pair A B b = ⊤
  rwa [iSup_bool_eq]
private noncomputable def cover2 (A B : X.Opens) (h : A ⊔ B = ⊤) : X.OpenCover :=
  X.openCoverOfIsOpenCover (pair A B) (isOpenCover_pair A B h)
private lemma isEmpty_pullback_ι (A B : X.Opens) (hd : A ⊓ B = ⊥) : IsEmpty ↑(pullback A.ι B.ι) := by
  refine ⟨fun p => ?_⟩
  have h1 : (pullback.fst A.ι B.ι ≫ A.ι).base p = (pullback.snd A.ι B.ι ≫ B.ι).base p := by
    rw [pullback.condition]
  rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, Scheme.Opens.ι_apply] at h1
  have hA : ((pullback.fst A.ι B.ι).base p).1 ∈ A := ((pullback.fst A.ι B.ι).base p).2
  have hB : ((pullback.snd A.ι B.ι).base p).1 ∈ B := ((pullback.snd A.ι B.ι).base p).2
  rw [← h1] at hB
  have hmem : ((pullback.fst A.ι B.ι).base p).1 ∈ A ⊓ B := ⟨hA, hB⟩
  rwa [hd] at hmem
private lemma glue2_compat
  (A B : X.Opens) (hd : A ⊓ B = ⊥) {T : (Scheme : Type (u + 1))}
  (fa : (A : (Scheme : Type (u + 1))) ⟶ T) (fb : (B : (Scheme : Type (u + 1))) ⟶ T)
  (i j : Bool) :
  pullback.fst (pair A B i).ι (pair A B j).ι ≫ cond i fa fb =
    pullback.snd (pair A B i).ι (pair A B j).ι ≫ cond j fa fb := by
  let _ := isEmpty_pullback_ι A B hd
  let _ := isEmpty_pullback_ι B A (by rwa [inf_comm])
  cases i
  ·
    cases j
    ·
      show pullback.fst B.ι B.ι ≫ fb = pullback.snd B.ι B.ι ≫ fb
      rw [fst_eq_snd_of_mono_eq]
    · apply (isInitialOfIsEmpty (X := pullback B.ι A.ι)).hom_ext
  ·
    cases j
    · apply (isInitialOfIsEmpty (X := pullback A.ι B.ι)).hom_ext
    ·
      show pullback.fst A.ι A.ι ≫ fa = pullback.snd A.ι A.ι ≫ fa
      rw [fst_eq_snd_of_mono_eq]
private noncomputable def glue2
  (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : (Scheme : Type (u + 1))}
  (fa : (A : (Scheme : Type (u + 1))) ⟶ T) (fb : (B : (Scheme : Type (u + 1))) ⟶ T) :
  X ⟶ T :=
  (cover2 A B h).glueMorphisms (fun b => cond b fa fb) (glue2_compat A B hd fa fb)
private lemma ι_glue2_left
  (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : (Scheme : Type (u + 1))}
  (fa : (A : (Scheme : Type (u + 1))) ⟶ T) (fb : (B : (Scheme : Type (u + 1))) ⟶ T) :
  A.ι ≫ glue2 A B h hd fa fb = fa :=
  Scheme.Cover.ι_glueMorphisms (cover2 A B h) _ _ true
private lemma ι_glue2_right
  (A B : X.Opens) (h : A ⊔ B = ⊤) (hd : A ⊓ B = ⊥) {T : (Scheme : Type (u + 1))}
  (fa : (A : (Scheme : Type (u + 1))) ⟶ T) (fb : (B : (Scheme : Type (u + 1))) ⟶ T) :
  B.ι ≫ glue2 A B h hd fa fb = fb :=
  Scheme.Cover.ι_glueMorphisms (cover2 A B h) _ _ false
private lemma hom_ext2
  (A B : X.Opens) (h : A ⊔ B = ⊤) {T : (Scheme : Type (u + 1))} (F G : X ⟶ T)
  (ha : A.ι ≫ F = A.ι ≫ G) (hb : B.ι ≫ F = B.ι ≫ G) :
  F = G :=
  Scheme.Cover.hom_ext (cover2 A B h) F G (fun b => by
    cases b
    · apply hb
    · apply ha)
private noncomputable def complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : X.Opens := ⟨(A : Set X)ᶜ, hA.isOpen_compl⟩
private lemma sup_complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : A ⊔ complOpen A hA = ⊤ :=
  Opens.ext (by simp [complOpen])
private lemma inf_complOpen (A : X.Opens) (hA : IsClosed (A : Set X)) : A ⊓ complOpen A hA = ⊥ :=
  Opens.ext (by simp [complOpen])
private lemma helper_main
  {M X : (Scheme : Type (u + 1))} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
  (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
  (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
  (hcat : ∀ (T : (Scheme : Type (u + 1))) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
  (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, ((TopologicalSpace.Opens.map (ρ h).hom.base).obj V) = V) :
  ∃ (U : X.Opens) (hUV : ((TopologicalSpace.Opens.map π.base).obj U) = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧ ∀ (T : (Scheme : Type (u + 1))) (f : (V : (Scheme : Type (u + 1))) ⟶ T), (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) → ∃! f' : (U : (Scheme : Type (u + 1))) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f := by
  classical
  let _ := hint
  have hstab : ∀ (h : H) (m : M), (ρ h).hom.base m ∈ V ↔ m ∈ V := fun h m => by
    rw [← mem_preimage_iff, hV h]
  have hsat : ∀ m : M, π.base m ∈ π.base '' (V : Set M) → m ∈ V := by
    rintro m ⟨v, hv, hvm⟩
    rw [horbit v m] at hvm
    obtain ⟨h, rfl⟩ := hvm
    rw [hstab h v]
    apply hv
  have hUcl : IsClosed (π.base '' (V : Set M)) := π.isClosedMap _ hVcl
  have hcompl : (π.base '' (V : Set M))ᶜ = π.base '' (V : Set M)ᶜ := by
    ext x
    constructor
    ·
      intro hx
      obtain ⟨m, rfl⟩ := hsurj x
      exact ⟨m, fun hm => hx ⟨m, hm, rfl⟩, rfl⟩
    ·
      rintro ⟨m, hm, rfl⟩ hx
      apply hm (hsat m hx)
  have hUop : IsOpen (π.base '' (V : Set M)) := by
    rw [← compl_compl (π.base '' (V : Set M)), hcompl]
    apply (π.isClosedMap _ V.isOpen.isClosed_compl).isOpen_compl
  let U : X.Opens := ⟨π.base '' (V : Set M), hUop⟩
  have hUV : ((TopologicalSpace.Opens.map π.base).obj U) = V := by
    ext m
    exact ⟨fun hm => hsat m hm, fun hm => ⟨m, hm, rfl⟩⟩
  let Vc : M.Opens := complOpen V hVcl
  let Uc : X.Opens := complOpen U hUcl
  have hVc : ∀ h : H, ((TopologicalSpace.Opens.map (ρ h).hom.base).obj Vc) = Vc := fun h => by
    ext m
    show (ρ h).hom.base m ∈ (V : Set M)ᶜ ↔ m ∈ (V : Set M)ᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff, SetLike.mem_coe, SetLike.mem_coe, hstab]
  have hUcVc : ((TopologicalSpace.Opens.map π.base).obj Uc) = Vc := by
    ext m
    show π.base m ∈ (π.base '' (V : Set M))ᶜ ↔ m ∈ (V : Set M)ᶜ
    rw [Set.mem_compl_iff, Set.mem_compl_iff, SetLike.mem_coe]
    exact ⟨fun hm hmV => hm ⟨m, hmV, rfl⟩, fun hm hx => hm (hsat m hx)⟩
  refine ⟨U, hUV, hUcl, rfl, ?_⟩
  intro T f hf
  let F : M ⟶ T ⨿ X := glue2 V Vc (sup_complOpen V hVcl) (inf_complOpen V hVcl)
    (f ≫ coprod.inl) (Vc.ι ≫ π ≫ coprod.inr)
  have hFV : V.ι ≫ F = f ≫ coprod.inl := ι_glue2_left _ _ _ _ _ _
  have hFVc : Vc.ι ≫ F = Vc.ι ≫ π ≫ coprod.inr := ι_glue2_right _ _ _ _ _ _
  have hFinv : ∀ h : H, (ρ h).hom ≫ F = F := by
    intro h
    apply hom_ext2 V Vc (sup_complOpen V hVcl)
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ρ h).hom (show V ≤ ((TopologicalSpace.Opens.map (ρ h).hom.base).obj V) by rw [hV h]),
        Category.assoc, hFV, ← Category.assoc, hf h]
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (ρ h).hom (show Vc ≤ ((TopologicalSpace.Opens.map (ρ h).hom.base).obj Vc) by rw [hVc h]),
        Category.assoc, hFVc, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, ← Category.assoc (ρ h).hom, hπ h]
  obtain ⟨Fbar, hFbar, hFbar_uniq⟩ := hcat _ F hFinv
  have hrange : Set.range (U.ι ≫ Fbar).base ⊆ Set.range (coprod.inl : T ⟶ T ⨿ X).base := by
    rintro _ ⟨u, rfl⟩
    obtain ⟨v, hv, hvu⟩ := u.2
    refine ⟨f.base ⟨v, hv⟩, ?_⟩
    have e1 : (U.ι ≫ Fbar).base u = Fbar.base (π.base v) := by
      rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply, ← hvu]
    have e2 : Fbar.base (π.base v) = F.base (V.ι.base ⟨v, hv⟩) := by
      rw [← Scheme.Hom.comp_apply, hFbar, Scheme.Opens.ι_apply]
    have e3 : F.base (V.ι.base ⟨v, hv⟩) = (coprod.inl : T ⟶ T ⨿ X).base (f.base ⟨v, hv⟩) := by
      rw [← Scheme.Hom.comp_apply, hFV, Scheme.Hom.comp_apply]
    rw [e1, e2, e3]
  let f' : (U : (Scheme : Type (u + 1))) ⟶ T := IsOpenImmersion.lift coprod.inl (U.ι ≫ Fbar) hrange
  have hf' : f' ≫ coprod.inl = U.ι ≫ Fbar := IsOpenImmersion.lift_fac _ _ _
  have hresV : π.resLE U V (by rw [hUV]) ≫ U.ι = V.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  have hresVc : π.resLE Uc Vc (by rw [hUcVc]) ≫ Uc.ι = Vc.ι ≫ π := Scheme.Hom.resLE_comp_ι _ _
  refine ⟨f', ?_, ?_⟩
  ·
    show π.resLE U V (by rw [hUV]) ≫ f' = f
    rw [← cancel_mono (coprod.inl : T ⟶ T ⨿ X), Category.assoc, hf', ← Category.assoc, hresV, Category.assoc, hFbar, hFV]
  ·
    intro f'' hf''
    let Fbar'' : X ⟶ T ⨿ X := glue2 U Uc (sup_complOpen U hUcl) (inf_complOpen U hUcl)
      (f'' ≫ coprod.inl) (Uc.ι ≫ coprod.inr)
    have h1 : U.ι ≫ Fbar'' = f'' ≫ coprod.inl := ι_glue2_left _ _ _ _ _ _
    have h2 : Uc.ι ≫ Fbar'' = Uc.ι ≫ coprod.inr := ι_glue2_right _ _ _ _ _ _
    have hπF : π ≫ Fbar'' = F := by
      apply hom_ext2 V Vc (sup_complOpen V hVcl)
      · rw [← Category.assoc, ← hresV, Category.assoc, h1, ← Category.assoc, hf'', hFV]
      · rw [← Category.assoc, ← hresVc, Category.assoc, h2, ← Category.assoc, hresVc, Category.assoc, hFVc]
    have heq : Fbar'' = Fbar := hFbar_uniq Fbar'' hπF
    rw [← cancel_mono (coprod.inl : T ⟶ T ⨿ X), hf', ← heq, h1]
/--
[AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_exists_opens_isClosed_preimage_eq_existsUnique_of_quotient.lean)
-/
@[path]
private lemma main
  {M X : (Scheme : Type (u + 1))} {H : Type} [Group H] [Finite H] (ρ : H →* Aut M) (π : M ⟶ X)
  (hπ : ∀ h : H, (ρ h).hom ≫ π = π) (hint : IsIntegralHom π) (hsurj : Function.Surjective π.base)
  (horbit : ∀ x x' : M, π.base x = π.base x' ↔ ∃ h : H, (ρ h).hom.base x = x')
  (hcat : ∀ (T : (Scheme : Type (u + 1))) (f : M ⟶ T), (∀ h : H, (ρ h).hom ≫ f = f) → ∃! f' : X ⟶ T, π ≫ f' = f)
  (V : M.Opens) (hVcl : IsClosed (V : Set M)) (hV : ∀ h : H, ((TopologicalSpace.Opens.map (ρ h).hom.base).obj V) = V) :
  ∃ (U : X.Opens) (hUV : ((TopologicalSpace.Opens.map π.base).obj U) = V), IsClosed (U : Set X) ∧ Set.image π.base (V : Set M) = (U : Set X) ∧ ∀ (T : (Scheme : Type (u + 1))) (f : (V : (Scheme : Type (u + 1))) ⟶ T), (∀ h : H, (ρ h).hom.resLE V V (by rw [hV h]) ≫ f = f) → ∃! f' : (U : (Scheme : Type (u + 1))) ⟶ T, π.resLE U V (by rw [hUV]) ≫ f' = f :=
  helper_main ρ π hπ hint hsurj horbit hcat V hVcl hV


-- created on 2026-10-20
