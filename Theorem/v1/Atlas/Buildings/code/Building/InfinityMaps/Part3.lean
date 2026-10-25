/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.Buildings.code.Building.InfinityConstruction.Part3
import Lemma.Set.PointsAtInfinity.of.Vertices
import Lemma.Finset.LabelMap.eq.ImageLabelMap.of.EqLabelMap_Head_ImageLabelMap_Head.IsChainAdjacent.Ne.All_EqLabelMap_ImageLabelMap
import Def.v1.Atlas.Buildings.code.Building.Labels
import Mathlib.Data.NNReal.Basic
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part4
set_option linter.unusedSectionVars false

open AffineBuilding

variable {V : Type} [DecidableEq V]


namespace AffineBuilding

/-- The induced map $\varphi_\infty$ commutes with the parallelism quotient on rays. -/
theorem BuildingIsometry.inducedMapInfinity_mk
    {b : Building V} {md : ApartmentMetricData b}
    (φ : BuildingIsometry b md)
    (ρ : GeodesicRay b md) :
    φ.inducedMapInfinity (Quot.mk _ ρ) =
      Quot.mk (GeodesicRay.Parallel b md) (φ.pushforwardRay ρ) := by
  rfl

/-- If a simplicial automorphism $f$ sends a sector's apartment into an
apartment $A'$, then the image $f(S)$ is again a sector with apartment $A'$. -/
theorem automorphism_maps_sectors_apartment
    {V : Type} [DecidableEq V]
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (S : Sector b) (A' : SimplicialComplex V)
    (hA' : A' ∈ b.apartmentSystem.apartments)
    (h_maps : ∀ s ∈ S.apartment.faces, s.image f ∈ A'.faces) :
    ∃ (S' : Sector b), S'.vertices = f '' S.vertices ∧ S'.apartment = A' := by


  obtain ⟨s_base, hs_base_face, h_bv_in_s⟩ := S.baseVertex_mem
  have h_img_base_face : s_base.image f ∈ A'.faces := h_maps s_base hs_base_face
  have h_fbv_in_img : f S.baseVertex ∈ s_base.image f := Finset.mem_image_of_mem f h_bv_in_s

  have h_singleton_face : {f S.baseVertex} ∈ A'.faces :=
    A'.down_closed h_img_base_face (Finset.singleton_subset_iff.mpr h_fbv_in_img)
      (Finset.singleton_nonempty _)

  have h_verts_in_apt : ∀ v ∈ f '' S.vertices, ∃ s ∈ A'.faces, v ∈ s := by
    intro v hv
    obtain ⟨u, hu_in, rfl⟩ := hv
    obtain ⟨s, hs_face, hu_in_s⟩ := S.vertices_in_apartment u hu_in
    exact ⟨s.image f, h_maps s hs_face, Finset.mem_image_of_mem f hu_in_s⟩

  have h_fbv_in_verts : f S.baseVertex ∈ f '' S.vertices :=
    ⟨S.baseVertex, S.baseVertex_in_sector, rfl⟩


  have h_sub : IsSubcomplex A' b.toChamberComplex.toSimplicialComplex :=
    b.apartmentSystem.sub A' hA'

  refine ⟨⟨A', hA', f S.baseVertex,
    ⟨s_base.image f, h_img_base_face, h_fbv_in_img⟩,
    f '' S.vertices, h_verts_in_apt, h_fbv_in_verts,
    Set.Nonempty.image f S.nonempty⟩, rfl, rfl⟩

/-- A simplicial automorphism sends every sector to another sector (in some
apartment of the building's system). -/
theorem automorphism_maps_sectors
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f)
    (S : Sector b) :
    ∃ (S' : Sector b), S'.vertices = f '' S.vertices := by
  obtain ⟨A', hA', hA'_faces⟩ := hf.maps_apartments S.apartment S.apartment_mem
  obtain ⟨S', hS', _⟩ := automorphism_maps_sectors_apartment f hf S A' hA'
    (fun s hs => hA'_faces s hs)
  exact ⟨S', hS'⟩

/-- An injective face-preserving map with a face-preserving two-sided inverse
sends maximal faces to maximal faces. -/
theorem injective_face_map_maximal
    {V : Type} [DecidableEq V]

    {K : SimplicialComplex V}
    (h : V → V) (h_inj : Function.Injective h)
    (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
    (h_inv : V → V) (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
    (h_inv_left : ∀ v, h_inv (h v) = v)
    (h_right : ∀ v, h (h_inv v) = v)
    (C : Finset V) (hC : K.IsMaximal C) :
    K.IsMaximal (C.image h) := by
  refine ⟨h_faces C hC.1, ?_⟩
  intro D hD hCD
  have h_Cinv : (C.image h).image h_inv = C := by
    rw [Finset.image_image]
    have : h_inv ∘ h = id := funext h_inv_left
    rw [this, Finset.image_id]
  have h_sub : C ⊆ D.image h_inv := by
    rw [← h_Cinv]; exact Finset.image_subset_image hCD
  have hD_inv_face : D.image h_inv ∈ K.faces := h_inv_faces D hD
  have hmax := hC.2 (D.image h_inv) hD_inv_face h_sub
  rw [hmax, Finset.image_image]
  have : h ∘ h_inv = id := funext h_right
  rw [this, Finset.image_id]

/-- Such a bijective face-preserving map also preserves chamber adjacency. -/
theorem injective_face_map_adjacent
    {V : Type} [DecidableEq V]
    {K : SimplicialComplex V}
    (h : V → V) (h_inj : Function.Injective h)
    (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
    (h_inv : V → V) (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
    (h_inv_left : ∀ v, h_inv (h v) = v)
    (h_right : ∀ v, h (h_inv v) = v)
    (C D : Finset V) (hadj : K.Adjacent C D) :
    K.Adjacent (C.image h) (D.image h) := by
  obtain ⟨hC_max, hD_max, hCD_ne, F, hF_C, hF_D⟩ := hadj
  refine ⟨injective_face_map_maximal h h_inj h_faces h_inv h_inv_faces h_inv_left h_right C hC_max,
          injective_face_map_maximal h h_inj h_faces h_inv h_inv_faces h_inv_left h_right D hD_max,
          ?_, F.image h, ?_, ?_⟩
  · intro heq; exact hCD_ne ((Finset.image_injective h_inj).eq_iff.mp heq)
  · constructor
    · exact ⟨h_faces F hF_C.1.1, h_faces C hC_max.1, Finset.image_subset_image hF_C.1.2.2⟩
    · rw [← Finset.image_sdiff_of_injOn (Set.injOn_of_injective h_inj) hF_C.1.2.2]
      rw [Finset.card_image_of_injective _ h_inj]
      exact hF_C.2
  · constructor
    · exact ⟨h_faces F hF_D.1.1, h_faces D hD_max.1, Finset.image_subset_image hF_D.1.2.2⟩
    · rw [← Finset.image_sdiff_of_injOn (Set.injOn_of_injective h_inj) hF_D.1.2.2]
      rw [Finset.card_image_of_injective _ h_inj]
      exact hF_D.2

/-- Every simplicial automorphism $f$ has a two-sided inverse $g$ which is
also a simplicial automorphism. -/
theorem inverse_is_automorphism
    {V : Type} [DecidableEq V]
    {b : Building V}
    (f : V → V) (hf : IsSimplicialAutomorphism b f) :
    ∃ (g : V → V), IsSimplicialAutomorphism b g ∧
      (∀ v, g (f v) = v) ∧ (∀ v, f (g v) = v) := by

  have hbij := hf.bijective
  obtain ⟨g, hfg⟩ := hbij.surjective.hasRightInverse
  have hgf : ∀ v, g (f v) = v := by
    intro v; exact hbij.injective (hfg (f v))
  have g_bij : Function.Bijective g := by
    constructor
    · intro a b hab
      have := congr_arg f hab
      rw [hfg a, hfg b] at this
      exact this
    · intro a; exact ⟨f a, hgf a⟩
  have f_inj : Function.Injective f := hbij.injective
  have g_inj : Function.Injective g := g_bij.injective

  have image_gf : ∀ t : Finset V, (t.image g).image f = t := by
    intro t
    rw [Finset.image_image]
    have : f ∘ g = id := funext hfg
    rw [this, Finset.image_id]

  have image_fg : ∀ t : Finset V, (t.image f).image g = t := by
    intro t
    rw [Finset.image_image]
    have : g ∘ f = id := funext hgf
    rw [this, Finset.image_id]

  let K := b.toChamberComplex.toSimplicialComplex

  have g_maps_faces : ∀ s ∈ K.faces, s.image g ∈ K.faces := by
    intro s hs
    obtain ⟨C, hC_max, hs_sub_C⟩ := b.toChamberComplex.exists_maximal s hs
    have h_sub : s.image g ⊆ C.image g := Finset.image_subset_image hs_sub_C
    suffices h_Cg : C.image g ∈ K.faces by
      have h_ne : (s.image g).Nonempty := by
        obtain ⟨v, hv⟩ := K.nonempty_of_mem s hs
        exact ⟨g v, Finset.mem_image_of_mem g hv⟩
      exact K.down_closed h_Cg h_sub h_ne
    obtain ⟨A, hA_mem, hC_in_A, _⟩ := b.apartmentSystem.contains_pair C C hC_max hC_max
    have h_strong := b.apartmentSystem.strong_iso_ext_gallery
      {C.image g} {C} (Finset.image f)
      (by intro t ht; simp only [Set.mem_singleton_iff] at ht ⊢; rw [ht]; exact image_gf C)
      (by intro t1 ht1 t2 ht2; simp only [Set.mem_singleton_iff] at ht1 ht2
          subst ht1; subst ht2; simp [galleryDist_self])
      ⟨A, hA_mem, by intro t ht; simp only [Set.mem_singleton_iff] at ht; rw [ht]; exact hC_in_A⟩
    obtain ⟨B, hB_mem, hB_contains⟩ := h_strong
    exact b.apartmentSystem.sub B hB_mem (hB_contains (C.image g) (Set.mem_singleton _))


  have f_gallery_dist : ∀ C D : Finset V,
      galleryDist K (C.image f) (D.image f) = galleryDist K C D := by
    intro C D
    by_cases hCD : C = D
    · subst hCD; simp [galleryDist_self]
    · have hCD_f : C.image f ≠ D.image f := by
        intro h; exact hCD ((Finset.image_injective f_inj).eq_iff.mp h)

      suffices h_eq : {n | ∃ γ : Gallery K, γ.Connects (C.image f) (D.image f) ∧ γ.length = n} =
          {n | ∃ γ : Gallery K, γ.Connects C D ∧ γ.length = n} by
        unfold galleryDist; rw [if_neg hCD_f, if_neg hCD, h_eq]
      ext n; constructor
      ·
        rintro ⟨γ, hγ_conn, hγ_len⟩
        let chambers' := γ.chambers.map (Finset.image g)
        have h_len' : chambers'.length > 0 := by
          simp [chambers', List.length_map]; exact γ.length_pos
        have h_max' : ∀ E ∈ chambers', K.IsMaximal E := by
          intro E hE
          rw [List.mem_map] at hE
          obtain ⟨E', hE'_mem, rfl⟩ := hE
          exact injective_face_map_maximal g g_inj g_maps_faces f hf.maps_faces hfg hgf
            E' (γ.all_maximal E' hE'_mem)
        have h_adj' : List.IsChain K.Adjacent chambers' :=
          List.isChain_map_of_isChain (Finset.image g)
            (fun A B hadj => injective_face_map_adjacent g g_inj g_maps_faces f hf.maps_faces
              hfg hgf A B hadj)
            γ.adjacent_consecutive
        have h_conn' : (⟨chambers', h_len', h_max', h_adj'⟩ : Gallery K).Connects C D := by
          simp only [Gallery.Connects] at hγ_conn ⊢
          constructor
          · show chambers'.head? = some C
            simp only [chambers', List.head?_map, hγ_conn.1, Option.map_some, image_fg]
          · show chambers'.getLast? = some D
            simp only [chambers', List.getLast?_map, hγ_conn.2, Option.map_some, image_fg]
        refine ⟨⟨chambers', h_len', h_max', h_adj'⟩, h_conn', ?_⟩
        show chambers'.length - 1 = n
        simp only [chambers', List.length_map]
        exact hγ_len
      ·
        rintro ⟨γ, hγ_conn, hγ_len⟩
        let chambers' := γ.chambers.map (Finset.image f)
        have h_len' : chambers'.length > 0 := by
          simp [chambers', List.length_map]; exact γ.length_pos
        have h_max' : ∀ E ∈ chambers', K.IsMaximal E := by
          intro E hE
          rw [List.mem_map] at hE
          obtain ⟨E', hE'_mem, rfl⟩ := hE
          exact injective_face_map_maximal f f_inj hf.maps_faces g g_maps_faces hgf hfg
            E' (γ.all_maximal E' hE'_mem)
        have h_adj' : List.IsChain K.Adjacent chambers' :=
          List.isChain_map_of_isChain (Finset.image f)
            (fun A B hadj => injective_face_map_adjacent f f_inj hf.maps_faces g g_maps_faces
              hgf hfg A B hadj)
            γ.adjacent_consecutive
        have h_conn' : (⟨chambers', h_len', h_max', h_adj'⟩ : Gallery K).Connects (C.image f) (D.image f) := by
          simp only [Gallery.Connects] at hγ_conn ⊢
          constructor
          · show chambers'.head? = some (C.image f)
            simp only [chambers', List.head?_map, hγ_conn.1, Option.map_some]
          · show chambers'.getLast? = some (D.image f)
            simp only [chambers', List.getLast?_map, hγ_conn.2, Option.map_some]
        refine ⟨⟨chambers', h_len', h_max', h_adj'⟩, h_conn', ?_⟩
        show chambers'.length - 1 = n
        simp only [chambers', List.length_map]
        exact hγ_len

  have g_maps_apartments : ∀ A ∈ b.apartmentSystem.apartments,
      ∃ A' ∈ b.apartmentSystem.apartments,
        ∀ s ∈ A.faces, s.image g ∈ A'.faces := by
    intro A' hA'_mem
    let S₂ : Set (Finset V) := { C | A'.IsMaximal C }
    let S₁ : Set (Finset V) := Finset.image g '' S₂
    have h_map : ∀ t ∈ S₁, Finset.image f t ∈ S₂ := by
      intro t ht
      obtain ⟨C, hC_max, rfl⟩ := ht
      show A'.IsMaximal ((C.image g).image f)
      rw [image_gf]; exact hC_max
    have h_dist : ∀ t1 ∈ S₁, ∀ t2 ∈ S₁,
        galleryDist K (Finset.image f t1) (Finset.image f t2) = galleryDist K t1 t2 := by
      intro t1 _ t2 _
      exact f_gallery_dist t1 t2
    have h_S₂_in_apt : ∃ A ∈ b.apartmentSystem.apartments, ∀ C ∈ S₂, C ∈ A.faces := by
      exact ⟨A', hA'_mem, fun C hC => hC.1⟩
    obtain ⟨B, hB_mem, hB_contains⟩ := b.apartmentSystem.strong_iso_ext_gallery S₁ S₂
      (Finset.image f) h_map h_dist h_S₂_in_apt

    refine ⟨B, hB_mem, ?_⟩
    intro s hs

    obtain ⟨_, _, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A' hA'_mem

    have hs_cc : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
    obtain ⟨C, hC_max_cc, hs_sub_C⟩ := cc.exists_maximal s hs_cc

    have hC_max_A' : A'.IsMaximal C := by
      rw [← hcc_eq]; exact ⟨hC_max_cc.1, hC_max_cc.2⟩
    have hCg_in_B : C.image g ∈ B.faces := by
      apply hB_contains
      exact ⟨C, hC_max_A', rfl⟩
    have h_sub : s.image g ⊆ C.image g := Finset.image_subset_image hs_sub_C
    have h_ne : (s.image g).Nonempty := by
      obtain ⟨v, hv⟩ := A'.nonempty_of_mem s hs
      exact ⟨g v, Finset.mem_image_of_mem g hv⟩
    exact B.down_closed hCg_in_B h_sub h_ne
  exact ⟨g, ⟨g_maps_faces, g_bij, g_maps_apartments⟩, hgf, hfg⟩

/-- Every simplicial automorphism of a building is an isometry with respect
to the apartment metric. -/
theorem automorphism_is_isometry
    {V : Type} [DecidableEq V]
    {b : Building V} (md : ApartmentMetricData b)
    (f : V → V) (hf : IsSimplicialAutomorphism b f) :
    ∀ v w : V, buildingDist b md (f v) (f w) = buildingDist b md v w := by
  intro v w
  simp only [buildingDist]
  by_cases h_vw : ∃ (A : { A // A ∈ b.apartmentSystem.apartments }),
      (∃ s ∈ A.val.faces, v ∈ s) ∧ (∃ s ∈ A.val.faces, w ∈ s)
  case pos =>
    obtain ⟨A, ⟨sv, hsv, hv_sv⟩, ⟨sw, hsw, hw_sw⟩⟩ := h_vw

    obtain ⟨A'_val, hA'_mem, hA'_faces⟩ := hf.maps_apartments A.val A.property
    let A' : { A // A ∈ b.apartmentSystem.apartments } := ⟨A'_val, hA'_mem⟩

    have h_fv_in_A' : ∃ s ∈ A'.val.faces, f v ∈ s :=
      ⟨sv.image f, hA'_faces sv hsv, Finset.mem_image_of_mem f hv_sv⟩
    have h_fw_in_A' : ∃ s ∈ A'.val.faces, f w ∈ s :=
      ⟨sw.image f, hA'_faces sw hsw, Finset.mem_image_of_mem f hw_sw⟩

    have h_fvfw : ∃ (B : { A // A ∈ b.apartmentSystem.apartments }),
        (∃ s ∈ B.val.faces, f v ∈ s) ∧ (∃ s ∈ B.val.faces, f w ∈ s) :=
      ⟨A', h_fv_in_A', h_fw_in_A'⟩
    have h_vw' : ∃ (B : { A // A ∈ b.apartmentSystem.apartments }),
        (∃ s ∈ B.val.faces, v ∈ s) ∧ (∃ s ∈ B.val.faces, w ∈ s) :=
      ⟨A, ⟨sv, hsv, hv_sv⟩, ⟨sw, hsw, hw_sw⟩⟩
    rw [dif_pos h_fvfw, dif_pos h_vw']


    obtain ⟨⟨s1, hs1, hfv1⟩, ⟨s2, hs2, hfw1⟩⟩ := h_fvfw.choose_spec
    have hfv_A' : {f v} ∈ A'.val.faces :=
      A'.val.down_closed (hA'_faces sv hsv) (Finset.singleton_subset_iff.mpr
        (Finset.mem_image_of_mem f hv_sv)) (Finset.singleton_nonempty _)
    have hfw_A' : {f w} ∈ A'.val.faces :=
      A'.val.down_closed (hA'_faces sw hsw) (Finset.singleton_subset_iff.mpr
        (Finset.mem_image_of_mem f hw_sw)) (Finset.singleton_nonempty _)
    have hfv_chosen : {f v} ∈ h_fvfw.choose.val.faces :=
      h_fvfw.choose.val.down_closed hs1 (Finset.singleton_subset_iff.mpr hfv1)
        (Finset.singleton_nonempty _)
    have hfw_chosen : {f w} ∈ h_fvfw.choose.val.faces :=
      h_fvfw.choose.val.down_closed hs2 (Finset.singleton_subset_iff.mpr hfw1)
        (Finset.singleton_nonempty _)
    have h_lhs_wd := buildingDist_well_defined_clean b md (f v) (f w)
      h_fvfw.choose A' hfv_chosen hfw_chosen hfv_A' hfw_A'

    obtain ⟨⟨s3, hs3, hv1⟩, ⟨s4, hs4, hw1⟩⟩ := h_vw'.choose_spec
    have hv_A : {v} ∈ A.val.faces :=
      A.val.down_closed hsv (Finset.singleton_subset_iff.mpr hv_sv)
        (Finset.singleton_nonempty _)
    have hw_A : {w} ∈ A.val.faces :=
      A.val.down_closed hsw (Finset.singleton_subset_iff.mpr hw_sw)
        (Finset.singleton_nonempty _)
    have hv_chosen : {v} ∈ h_vw'.choose.val.faces :=
      h_vw'.choose.val.down_closed hs3 (Finset.singleton_subset_iff.mpr hv1)
        (Finset.singleton_nonempty _)
    have hw_chosen : {w} ∈ h_vw'.choose.val.faces :=
      h_vw'.choose.val.down_closed hs4 (Finset.singleton_subset_iff.mpr hw1)
        (Finset.singleton_nonempty _)
    have h_rhs_wd := buildingDist_well_defined_clean b md v w h_vw'.choose A
      hv_chosen hw_chosen hv_A hw_A

    let φ : SimplicialMap A.val A'.val := ⟨f, fun s hs => hA'_faces s hs⟩
    have h_iso := md.iso_isometry A A' φ φ.map_face v w

    rw [h_lhs_wd, ← h_iso, h_rhs_wd]
  case neg =>


    have h_neg_fw : ¬∃ (A : { A // A ∈ b.apartmentSystem.apartments }),
        (∃ s ∈ A.val.faces, f v ∈ s) ∧ (∃ s ∈ A.val.faces, f w ∈ s) := by
      intro ⟨A', ⟨sv', hsv', hfv'⟩, ⟨sw', hsw', hfw'⟩⟩
      apply h_vw

      obtain ⟨g, hg_auto, hgf, _hfg⟩ := inverse_is_automorphism f hf

      obtain ⟨B, hB_mem, hB_maps⟩ := hg_auto.maps_apartments A'.val A'.property

      have h_sv_g : sv'.image g ∈ B.faces := hB_maps sv' hsv'
      have h_v_in : v ∈ sv'.image g := by
        rw [Finset.mem_image]
        exact ⟨f v, hfv', hgf v⟩

      have h_sw_g : sw'.image g ∈ B.faces := hB_maps sw' hsw'
      have h_w_in : w ∈ sw'.image g := by
        rw [Finset.mem_image]
        exact ⟨f w, hfw', hgf w⟩
      exact ⟨⟨B, hB_mem⟩, ⟨sv'.image g, h_sv_g, h_v_in⟩, ⟨sw'.image g, h_sw_g, h_w_in⟩⟩
    rw [dif_neg h_neg_fw, dif_neg h_vw]

end AffineBuilding
