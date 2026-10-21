import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

variable {X : (Scheme : Type (u + 1))}

private noncomputable def push (V : X.Opens) (S : Ideal (X.presheaf.obj (op V))) : X.IdealSheafData :=
  (Scheme.IdealSheafData.ofIdealTop (S.map (V.ι.appLE V ⊤ V.ι_preimage_self.ge).hom)).map V.ι
private lemma quasiCompact_ι
  {V : X.Opens} [QuasiSeparatedSpace X]
  -- given
  (hV : IsAffineOpen V) :
  -- imply
  QuasiCompact V.ι := by
  -- proof
  let _ : IsAffine V := hV
  let _ : QuasiSeparated (Limits.terminal.from X) :=
    Iff.mp (quasiSeparatedSpace_iff_quasiSeparated X) inferInstance
  apply MorphismProperty.of_postcomp @QuasiCompact (W' := @QuasiSeparated) V.ι (Limits.terminal.from X) inferInstance
  rw [Limits.terminal.comp_from]
  apply Iff.mpr (HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)) inferInstance
private lemma mem_ker_ideal_iff
  {Y : (Scheme : Type (u + 1))} (g : Y ⟶ X) [QuasiCompact g] (U : X.affineOpens)
  {κ : Type u} (W : κ → X.affineOpens)
  -- given
  (hWU : ∀ m, (W m : X.Opens) ≤ U)
  (hcov : ((TopologicalSpace.Opens.map g.base).obj (U : X.Opens)) ≤ ⨆ m : κ, ((TopologicalSpace.Opens.map g.base).obj (W m : X.Opens)))
  (t : X.presheaf.obj (op U)) :
  -- imply
  t ∈ g.ker.ideal U ↔ ∀ m, (X.presheaf.map (homOfLE (hWU m)).op).hom t ∈ g.ker.ideal (W m) := by
  -- proof
  simp only [Scheme.Hom.ker_apply, RingHom.mem_ker]
  have hnat : ∀ m, (g.app (W m)).hom ((X.presheaf.map (homOfLE (hWU m)).op).hom t) =
    (Y.presheaf.map (homOfLE (g.preimage_mono (hWU m))).op).hom ((g.app U).hom t) := by
    intro m
    change (X.presheaf.map (homOfLE (hWU m)).op ≫ g.app (W m)).hom t = (g.app U ≫ _).hom t
    rw [g.naturality]
    rfl
  constructor
  ·
    intro h m
    rw [hnat, h, map_zero]
  ·
    intro h
    apply Y.sheaf.eq_of_locally_eq' (fun m : κ => ((TopologicalSpace.Opens.map g.base).obj (W m : X.Opens))) (((TopologicalSpace.Opens.map g.base).obj (U : X.Opens)))
      (fun m : κ => homOfLE (g.preimage_mono (hWU m))) hcov
    intro m
    change (Y.presheaf.map (homOfLE (g.preimage_mono (hWU m))).op).hom ((g.app U).hom t) =
      (Y.presheaf.map (homOfLE (g.preimage_mono (hWU m))).op).hom 0
    rw [map_zero]
    apply (hnat m).symm.trans (h m)
private lemma push_eq_ker (V : X.Opens) (S : Ideal (X.presheaf.obj (op V))) :
  -- imply
  push V S = ((Scheme.IdealSheafData.ofIdealTop
    (S.map (V.ι.appLE V ⊤ V.ι_preimage_self.ge).hom)).subschemeι ≫ V.ι).ker := rfl
private lemma image_preimage_eq
  {V W : X.Opens}
  -- given
  (hWV : W ≤ V) :
  -- imply
  ((Scheme.Hom.opensFunctor V.ι).obj ((TopologicalSpace.Opens.map V.ι.base).obj W)) = W := by
  -- proof
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, Iff.mpr inf_eq_right hWV]
private lemma isAffineOpen_ι_preimage
  {V : X.Opens} (W : X.affineOpens)
  -- given
  (hWV : (W : X.Opens) ≤ V) :
  -- imply
  IsAffineOpen (((TopologicalSpace.Opens.map V.ι.base).obj (W : X.Opens))) := by
  -- proof
  rw [← V.ι.isAffineOpen_iff_of_isOpenImmersion, image_preimage_eq hWV]
  apply W.2
private lemma push_ideal
  [QuasiSeparatedSpace X] {V : X.Opens} (hV : IsAffineOpen V) (S : Ideal (X.presheaf.obj (op V)))
  (W : X.affineOpens)
  -- given
  (hWV : (W : X.Opens) ≤ V) :
  -- imply
  (push V S).ideal W = S.map (X.presheaf.map (homOfLE hWV).op).hom := by
  -- proof
  let _ := quasiCompact_ι hV
  rw [push, Scheme.IdealSheafData.ideal_map _ _ W (isAffineOpen_ι_preimage W hWV),
    Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_map, ← CommRingCat.hom_comp,
    Scheme.Hom.appLE_map, Scheme.Opens.ι_appLE]
  have h₁ : ((Scheme.Hom.opensFunctor V.ι).obj ((TopologicalSpace.Opens.map V.ι.base).obj (W : X.Opens))) ≤ W :=
    (image_preimage_eq hWV).le
  have h₂ : ((Scheme.Hom.opensFunctor V.ι).obj ((TopologicalSpace.Opens.map V.ι.base).obj (W : X.Opens))) ≤ V :=
    h₁.trans hWV
  have hcomp : (X.presheaf.map (homOfLE h₂).op).hom =
    (X.presheaf.map (homOfLE h₁).op).hom.comp (X.presheaf.map (homOfLE hWV).op).hom := by
    rw [← CommRingCat.hom_comp, ← X.presheaf.map_comp]
    rfl
  have hφbij : Function.Bijective (X.presheaf.map (homOfLE h₁).op).hom := by
    have : homOfLE h₁ = eqToHom (image_preimage_eq hWV) := Subsingleton.elim _ _
    rw [this, eqToHom_op]
    apply ConcreteCategory.bijective_of_isIso (X.presheaf.map (eqToHom _))
  change Ideal.comap (X.presheaf.map (homOfLE h₁).op).hom
    (Ideal.map (X.presheaf.map (homOfLE h₂).op).hom S) =
    Ideal.map (X.presheaf.map (homOfLE hWV).op).hom S
  rw [hcomp, ← Ideal.map_map, Ideal.comap_map_of_bijective _ hφbij]
private lemma exists_isNilpotent
  [CompactSpace X] [QuasiSeparatedSpace X]
  (I : X.IdealSheafData) (hI : I ≤ X.nilradical) (U : X.affineOpens) (s : X.presheaf.obj (op U))
  -- given
  (hs : s ∈ I.ideal U) :
  -- imply
  ∃ J : X.IdealSheafData, J ≤ I ∧ IsNilpotent J ∧ s ∈ J.ideal U := by
  -- proof
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun V : X.affineOpens => ((V : X.Opens) : Set X))
    (fun V => (V : X.Opens).2) (fun x _ => by
      obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      apply Iff.mpr Set.mem_iUnion
      exact ⟨⟨V, hV⟩, hxV⟩)
  have htcov : ⨆ V : t, ((V : X.affineOpens) : X.Opens) = ⊤ := by
    refine Iff.mp top_le_iff fun x _ => ?_
    have := ht (Set.mem_univ x)
    simp only [Set.mem_iUnion] at this
    obtain ⟨V, hV, hxV⟩ := this
    apply Iff.mpr Opens.mem_iSup
    exact ⟨⟨V, hV⟩, hxV⟩
  have hA : ∀ V : X.affineOpens, ∃ G : Finset (X.presheaf.obj (op V)), (∀ g ∈ G, X.basicOpen g ≤ (U : X.Opens)) ∧
      ((U : Set X) ∩ (V : X.Opens) ⊆ ⋃ g ∈ G, (X.basicOpen g : Set X)) := by
    intro V
    have hc : IsCompact (((U : X.Opens) : Set X) ∩ (V : X.Opens)) :=
      QuasiSeparatedSpace.inter_isCompact _ _ (U : X.Opens).2 U.2.isCompact (V : X.Opens).2 V.2.isCompact
    have H : ∀ x : (((U : X.Opens) : Set X) ∩ (V : X.Opens) : Set X), ∃ g : X.presheaf.obj (op V),
        X.basicOpen g ≤ (U : X.Opens) ∧ (x : X) ∈ X.basicOpen g := by
      rintro ⟨x, hxU, hxV⟩
      obtain ⟨g, hg, hxg⟩ := V.2.exists_basicOpen_le (V := (U : X.Opens) ⊓ V) ⟨x, ⟨hxU, hxV⟩⟩ hxV
      exact ⟨g, hg.trans inf_le_left, hxg⟩
    choose g hg hxg using H
    obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun x => (X.basicOpen (g x) : Set X))
      (fun x => (X.basicOpen (g x)).2) (fun x hx => Iff.mpr Set.mem_iUnion ⟨⟨x, hx⟩, hxg _⟩)
    refine ⟨T.image g, ?_, ?_⟩
    ·
      intro g' hg'
      obtain ⟨x, -, rfl⟩ := Iff.mp Finset.mem_image hg'
      apply hg x
    ·
      intro x hx
      have := hT hx
      simp only [Set.mem_iUnion] at this
      obtain ⟨y, hy, hxy⟩ := this
      apply Iff.mpr Set.mem_iUnion₂
      exact ⟨g y, Finset.mem_image_of_mem g hy, hxy⟩
  choose G hG₁ hG₂ using hA
  have hB : ∀ (V : X.affineOpens) (g : X.presheaf.obj (op V)) (hg : X.basicOpen g ≤ (U : X.Opens)),
      ∃ F : Finset (X.presheaf.obj (op V)), (↑F ⊆ (I.ideal V : Set (X.presheaf.obj (op V)))) ∧
        (X.presheaf.map (homOfLE hg).op).hom s ∈
          Ideal.span ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom '' F) := by
    intro V g hg
    have h0 : (X.presheaf.map (homOfLE hg).op).hom s ∈ I.ideal (X.affineBasicOpen g) := by
      rw [← I.map_ideal (show X.affineBasicOpen g ≤ U from hg)]
      apply Ideal.mem_map_of_mem _ hs
    rw [← I.map_ideal (show X.affineBasicOpen g ≤ V from X.basicOpen_le g)] at h0
    have h1 : (X.presheaf.map (homOfLE hg).op).hom s ∈ Submodule.span (X.presheaf.obj (op (X.basicOpen g)))
      ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom '' (I.ideal V)) := h0
    obtain ⟨T, hT, hsT⟩ := Submodule.mem_span_finite_of_mem_span h1
    obtain ⟨F, hF, hFT⟩ := Iff.mp Finset.subset_set_image_iff hT
    refine ⟨F, hF, ?_⟩
    rwa [← hFT, Finset.coe_image] at hsT
  choose F hFI hsF using hB
  let FV : ∀ V : X.affineOpens, Finset (X.presheaf.obj (op V)) := fun V =>
    (G V).attach.biUnion fun g => F V g.1 (hG₁ V g.1 g.2)
  let S : ∀ V : X.affineOpens, Ideal (X.presheaf.obj (op V)) := fun V => Ideal.span (FV V)
  have hSI : ∀ V, S V ≤ I.ideal V := by
    intro V
    refine Iff.mpr Ideal.span_le fun x hx => ?_
    obtain ⟨g, -, hx⟩ := Iff.mp Finset.mem_biUnion hx
    apply hFI V g.1 (hG₁ V g.1 g.2) hx
  have hSnil : ∀ V, IsNilpotent (S V) := by
    intro V
    refine Iff.mpr (Ideal.FG.isNilpotent_iff_le_nilradical ⟨FV V, rfl⟩) ((hSI V).trans ?_)
    refine (hI V).trans ?_
    change ((⊥ : X.IdealSheafData).radical).ideal V ≤ nilradical _
    rw [Scheme.IdealSheafData.radical_ideal, Scheme.IdealSheafData.ideal_bot]
    apply le_rfl
  let J : X.IdealSheafData := I ⊓ ⨅ V : t, push (V.1 : X.Opens) (S V.1)
  have hJV : ∀ V : t, J.ideal V.1 ≤ S V.1 := by
    intro V
    have h1 : J ≤ push (V.1 : X.Opens) (S V.1) := inf_le_right.trans (iInf_le _ V)
    refine (Scheme.IdealSheafData.ideal_mono h1 V.1).trans ?_
    rw [push_ideal V.1.2 (S V.1) V.1 le_rfl]
    have : (X.presheaf.map (homOfLE (le_rfl : (V.1 : X.Opens) ≤ V.1)).op).hom = RingHom.id _ := by
      have : (homOfLE (le_rfl : (V.1 : X.Opens) ≤ V.1)).op = 𝟙 _ := Subsingleton.elim _ _
      rw [this, X.presheaf.map_id]
      rfl
    rw [this, Ideal.map_id]
  refine ⟨J, inf_le_left, ?_, hs, ?_⟩
  ·
    choose n hn using hSnil
    refine ⟨Finset.univ.sup fun V : t => n V.1, ?_⟩
    rw [Scheme.IdealSheafData.zero_eq_bot]
    refine Scheme.IdealSheafData.ext_of_iSup_eq_top (fun V : t => V.1) htcov fun V => ?_
    rw [Scheme.IdealSheafData.ideal_pow, Scheme.IdealSheafData.ideal_bot]
    change J.ideal V.1 ^ (Finset.univ.sup fun V : t => n V.1) = ⊥
    rw [← le_bot_iff]
    have hle : n V.1 ≤ Finset.univ.sup fun V : t => n V.1 :=
      Finset.le_sup (f := fun V : t => n V.1) (Finset.mem_univ V)
    calc
      _ ≤ S V.1 ^ (Finset.univ.sup fun V : t => n V.1) := Ideal.pow_right_mono (hJV V) _
      _ ≤ S V.1 ^ n V.1 := Ideal.pow_le_pow_right hle
      _ = ⊥ := hn V.1
  ·
    change s ∈ (⨅ V : t, push (V.1 : X.Opens) (S V.1)).ideal U
    rw [Scheme.IdealSheafData.ideal_iInf, iInf_apply, Ideal.mem_iInf]
    intro V
    let _ := quasiCompact_ι V.1.2
    rw [push_eq_ker]
    refine Iff.mpr (mem_ker_ideal_iff _ U (fun g : G V.1 => X.affineBasicOpen g.1) (fun g => hG₁ V.1 g.1 g.2) ?_ s) (fun g => ?_)
    ·
      intro x hx
      have hxV : (((Scheme.IdealSheafData.ofIdealTop _).subschemeι ≫ (V.1 : X.Opens).ι) x : X) ∈
        ((V.1 : X.affineOpens) : X.Opens) := by
        rw [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
        apply Subtype.prop
      have := hG₂ V.1 ⟨hx, hxV⟩
      simp only [Set.mem_iUnion] at this
      obtain ⟨g, hg, hxg⟩ := this
      apply Iff.mpr Opens.mem_iSup
      exact ⟨⟨g, hg⟩, hxg⟩
    ·
      rw [← push_eq_ker, push_ideal V.1.2 (S V.1) (X.affineBasicOpen g.1) (X.basicOpen_le g.1),
        Ideal.map_span]
      refine Ideal.span_mono ?_ (hsF V.1 g.1 (hG₁ V.1 g.1 g.2))
      refine Set.image_mono ?_
      intro x hx
      apply Iff.mpr Finset.mem_biUnion
      exact ⟨⟨g.1, g.2⟩, Finset.mem_attach _ _, hx⟩
/--
[AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_exists_le_isNilpotent_mem_ideal_of_le_nilradical.lean)
-/
@[path]
private lemma main
  {X : (Scheme : Type (u + 1))} [CompactSpace X] [QuasiSeparatedSpace X]
  (I : X.IdealSheafData) (hI : I ≤ X.nilradical) (U : X.affineOpens) (s : X.presheaf.obj (op U))
  -- given
  (hs : s ∈ I.ideal U) :
  -- imply
  ∃ J : X.IdealSheafData, J ≤ I ∧ IsNilpotent J ∧ s ∈ J.ideal U :=
  exists_isNilpotent I hI U s hs


-- created on 2026-10-20
