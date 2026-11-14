import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.MaximalApartments.Part2


/--
[bij_iso_fixing_chamber_is_id_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma bij_iso_fixing_chamber_is_id_gen
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜 : ApartmentSystem b.toChamberComplex}
  {B B' : SimplicialComplex V}
  {D : Finset V}
  {φ : V → V}
-- given
  (hB : B ∈ 𝒜.apartments)
  (hD_B : D ∈ B.faces)
  (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D)
  (hφ_bij : Function.Bijective φ)
  (_hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
  (hφ_D : D.image φ = D) :
-- imply
  ∀ s ∈ B.faces, s.image φ = s := by
-- proof
  have hD_max_B : B.IsMaximal D :=
    𝒜.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
  have hmono_id : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t → s ⊂ t := by
    intro s t _ _ h; exact h
  have hmono_φ : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t →
    s.image φ ⊂ t.image φ := by
    intro s t _ _ hst
    exact finset_image_ssubset_of_injective hφ_bij.1 hst
  obtain ⟨_, hprop⟩ := 𝒜.apt_unique_labelling B hB
    V V id (fun s => s.image φ) hmono_id hmono_φ D hD_max_B
  have h_agree_D : D.image φ = (id D).image (id : V → V) := by
    simp [hφ_D]
  intro s hs
  have := hprop id Function.bijective_id h_agree_D s hs
  simp at this
  exact this

/--
[apt_automorphism_sending_chamber_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma apt_automorphism_sending_chamber_gen
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜 : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hA : A ∈ 𝒜.apartments)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  obtain ⟨B_idx, M, cc, hcc, φ, hinj, hsurj, hadj, hThin⟩ := 𝒜.apt_is_coxeter A hA
  have hCox : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (φ : Finset V → M.Group),
    (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
    (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧
    (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) :=
    ⟨B_idx, M, φ, hinj, hsurj, hadj⟩
  have hWR : ∀ C D : Finset V, A.Adjacent C D →
    ∃ wr : ChamberComplex.WallReflection cc, D.image wr.refl = C :=
    coxeter_apt_wall_reflections cc A hcc hThin hCox
  exact ChamberComplex.apt_vertex_level_automorphism A cc hcc hWR C D hC hD

/--
[apt_faces_subset_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma apt_faces_subset_gen
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜 : ApartmentSystem b.toChamberComplex}
  {A B : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜.apartments)
  (hB : B ∈ 𝒜.apartments)
  (hCA : C ∈ A.faces)
  (hCB : C ∈ B.faces)
  (hCmax : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
-- imply
  B.faces ⊆ A.faces := by
-- proof
  have hCmax_A : A.IsMaximal C :=
    𝒜.building_maximal_in_apt_is_apt_maximal A hA C hCA hCmax
  obtain ⟨φ, hφ_bij, hφ_faces⟩ :=
    𝒜.iso_bijective A hA B hB C hCA hCB hCmax_A
  have hCφ_max_B : B.IsMaximal (C.image φ) :=
    bijective_face_iso_preserves_maximal hφ_bij hφ_faces hCmax_A
  have hCmax_B : B.IsMaximal C :=
    𝒜.building_maximal_in_apt_is_apt_maximal B hB C hCB hCmax
  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber_gen b 𝒜 B hB C hCmax_B (C.image φ) hCφ_max_B
  let ψ := α ∘ φ
  have hψ_bij : Function.Bijective ψ := hα_bij.comp hφ_bij
  have hψ_faces : ∀ s, s ∈ A.faces ↔ s.image ψ ∈ B.faces := by
    intro s
    simp only [ψ, ← Finset.image_image]
    exact Iff.trans (hφ_faces s) (hα_faces (s.image φ))
  have hψ_C : C.image ψ = C := by
    simp only [ψ, ← Finset.image_image]
    exact hα_send
  have hψ_id : ∀ s ∈ A.faces, s.image ψ = s :=
    bij_iso_fixing_chamber_is_id_gen b 𝒜 A B hA C hCA hCmax ψ hψ_bij hψ_faces hψ_C
  have hA_sub_B : A.faces ⊆ B.faces := by
    intro t ht
    have h1 : t.image ψ ∈ B.faces := (hψ_faces t).mp ht
    rwa [hψ_id t ht] at h1
  intro s hs
  let e := Equiv.ofBijective ψ hψ_bij
  let t := s.image e.symm
  have ht_img : t.image ψ = s := by
    show (s.image e.symm).image e = s
    rw [Finset.image_image]
    simp only [Equiv.self_comp_symm, Finset.image_id]
  have ht_A : t ∈ A.faces := (hψ_faces t).mpr (ht_img ▸ hs)
  have hs_eq : s = t := ht_img.symm.trans (hψ_id t ht_A)
  exact hs_eq ▸ ht_A

/--
[building_faces_subset_apt_gen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma building_faces_subset_apt_gen
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜 : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜.apartments)
  (hCA : C ∈ A.faces)
  (hCmax : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
-- imply
  ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces := by
-- proof
  intro s hs
  obtain ⟨E, hE_max, hs_sub⟩ := b.toChamberComplex.exists_maximal s hs
  obtain ⟨B, hB, hCB, hEB⟩ := 𝒜.contains_pair C E hCmax hE_max
  have hs_B : s ∈ B.faces :=
    B.down_closed hEB hs_sub
      (b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs)
  exact apt_faces_subset_gen b 𝒜 A B hA hB C hCA hCB hCmax hs_B

/--
[cross_system_retraction_pair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_retraction_pair
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  ∃ (ρ σ : V → V), (∀ s ∈ A.faces, s.image ρ ∈ A'.faces) ∧ (∀ s ∈ A'.faces, s.image σ ∈ A.faces) ∧ (∀ v, σ (ρ v) = v) ∧ (∀ v, ρ (σ v) = v) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → ρ v = v) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → σ v = v) := by
-- proof
  have hCmax_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C :=
    𝒜₁.maximal_in_apt_is_maximal A hA C hCmax
  have hCA : C ∈ A.faces := hCmax.1
  have bldg_sub_A : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A.faces :=
    building_faces_subset_apt_gen b 𝒜₁ A hA C hCA hCmax_bldg
  have bldg_sub_A' : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s ∈ A'.faces :=
    building_faces_subset_apt_gen b 𝒜₂ A' hA' C hCA' hCmax_bldg
  have hA_sub_A' : A.faces ⊆ A'.faces := by
    intro s hs
    exact bldg_sub_A' s (𝒜₁.sub A hA hs)
  have hA'_sub_A : A'.faces ⊆ A.faces := by
    intro s hs
    exact bldg_sub_A s (𝒜₂.sub A' hA' hs)
  refine ⟨id, id, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    simp
    exact hA_sub_A' hs
  ·
    intro s hs
    simp
    exact hA'_sub_A hs
  ·
    intro v; rfl
  ·
    intro v; rfl
  ·
    intro v _ _; rfl
  ·
    intro v _ _; rfl

/--
[cross_system_iso_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_iso_exists
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  ∃ φ : SimplicialMap A A', Function.Bijective φ.toFun ∧ (∀ s, s ∈ A.faces ↔ s.image φ.toFun ∈ A'.faces) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v) := by
-- proof
  obtain ⟨ρ, σ, hρ_face, hσ_face, hσρ, hρσ, hρ_fix, _hσ_fix⟩ :=
    cross_system_retraction_pair b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA'
  refine ⟨⟨ρ, hρ_face⟩, ?_, ?_, ?_, ?_⟩
  · exact ⟨Function.LeftInverse.injective hσρ, Function.RightInverse.surjective hρσ⟩
  · intro s
    constructor
    · exact hρ_face s
    · intro hsρ
      have h1 : (s.image ρ).image σ ∈ A.faces := hσ_face (s.image ρ) hsρ
      rw [Finset.image_image] at h1
      have h2 : s.image (σ ∘ ρ) = s := by
        ext v
        simp only [Finset.mem_image, Function.comp]
        constructor
        · rintro ⟨w, hw, rfl⟩; rwa [hσρ w]
        · intro hv; exact ⟨v, hv, hσρ v⟩
      rwa [h2] at h1
  · exact hρ_fix
  · intro v hv
    exact hρ_fix v ⟨C, hCmax.1, hv⟩ ⟨C, hCA', hv⟩

/--
[cross_system_iso_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_iso_bijective
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (_hCA : C ∈ A.faces)
  (hCA' : C ∈ A'.faces)
  (hCmax : A.IsMaximal C) :
-- imply
  ∃ φ : V → V, Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ v = v) := by
-- proof
  obtain ⟨φ, hbij, hfaces, hfix, _⟩ :=
    cross_system_iso_exists b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA'
  exact ⟨φ.toFun, hbij, hfaces, hfix⟩

/--
[cross_system_iso_preserves_labels](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_iso_preserves_labels
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {L : Type}
  [DecidableEq L]
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
  {lab : Labelling b.toChamberComplex.toSimplicialComplex L}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  ∃ φ : SimplicialMap A A', (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) ∧ (∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s) := by
-- proof
  obtain ⟨φ, hbij, _hfaces, hfix, _hfixC⟩ :=
    cross_system_iso_exists b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA'
  refine ⟨φ, hfix, ?_⟩
  intro s hs
  have hA_sub : IsSubcomplex A b.toChamberComplex.toSimplicialComplex :=
    𝒜₁.sub A hA
  have hA'_sub : IsSubcomplex A' b.toChamberComplex.toSimplicialComplex :=
    𝒜₂.sub A' hA'
  have hinj := hbij.1
  have hmono1 : ∀ s' t', s' ∈ A.faces → t' ∈ A.faces → s' ⊂ t' →
    lab.labelMap s' ⊂ lab.labelMap t' := by
    intro s' t' hs' ht' hst
    exact lab.label_strictMono s' t' (hA_sub hs') (hA_sub ht') hst
  have hmono2 : ∀ s' t', s' ∈ A.faces → t' ∈ A.faces → s' ⊂ t' →
    lab.labelMap (s'.image φ.toFun) ⊂ lab.labelMap (t'.image φ.toFun) := by
    intro s' t' hs' ht' hst
    have hs'_A' := φ.map_face s' hs'
    have ht'_A' := φ.map_face t' ht'
    have h_img_ssubset : s'.image φ.toFun ⊂ t'.image φ.toFun := by
      constructor
      · exact Finset.image_subset_image hst.1
      · intro heq
        apply hst.2
        intro x hxt
        have hρx : φ.toFun x ∈ t'.image φ.toFun := Finset.mem_image_of_mem _ hxt
        have hρx_s : φ.toFun x ∈ s'.image φ.toFun := heq hρx
        rw [Finset.mem_image] at hρx_s
        obtain ⟨y, hy, hρeq⟩ := hρx_s
        exact hinj hρeq ▸ hy
    exact lab.label_strictMono _ _ (hA'_sub hs'_A') (hA'_sub ht'_A') h_img_ssubset
  have uniq := 𝒜₁.apt_unique_labelling A hA L L
    lab.labelMap (fun s' => lab.labelMap (s'.image φ.toFun))
    hmono1 hmono2 C hCmax
  have hC_fix : C.image φ.toFun = C := by
    ext v; simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : φ.toFun w = w := hfix w ⟨C, hCmax.1, hw⟩ ⟨C, hCA', hw⟩
      rw [this]; exact hw
    · intro hv; exact ⟨v, hv, hfix v ⟨C, hCmax.1, hv⟩ ⟨C, hCA', hv⟩⟩
  have h_agree : lab.labelMap (C.image φ.toFun) = (lab.labelMap C).image id := by
    simp [hC_fix]
  have h_part2 := uniq.2 id Function.bijective_id h_agree s hs
  simp at h_part2
  exact h_part2

/--
[any_iso_fixing_intersection_preserves_labels](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma any_iso_fixing_intersection_preserves_labels
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {L : Type}
  [DecidableEq L]
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
  {lab : Labelling b.toChamberComplex.toSimplicialComplex L}
  {φ : SimplicialMap A A'}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces)
  (hφ_bij : Function.Bijective φ.toFun)
  (hφ_fix : ∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) :
-- imply
  ∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s := by
-- proof
  have hA_sub : IsSubcomplex A b.toChamberComplex.toSimplicialComplex :=
    𝒜₁.sub A hA
  have hA'_sub : IsSubcomplex A' b.toChamberComplex.toSimplicialComplex :=
    𝒜₂.sub A' hA'
  have hinj := hφ_bij.1
  have hmono1 : ∀ s' t', s' ∈ A.faces → t' ∈ A.faces → s' ⊂ t' →
    lab.labelMap s' ⊂ lab.labelMap t' := by
    intro s' t' hs' ht' hst
    exact lab.label_strictMono s' t' (hA_sub hs') (hA_sub ht') hst
  have hmono2 : ∀ s' t', s' ∈ A.faces → t' ∈ A.faces → s' ⊂ t' →
    lab.labelMap (s'.image φ.toFun) ⊂ lab.labelMap (t'.image φ.toFun) := by
    intro s' t' hs' ht' hst
    have hs'_A' := φ.map_face s' hs'
    have ht'_A' := φ.map_face t' ht'
    have h_img_ssubset : s'.image φ.toFun ⊂ t'.image φ.toFun := by
      constructor
      · exact Finset.image_subset_image hst.1
      · intro heq
        apply hst.2
        intro x hxt
        have hρx : φ.toFun x ∈ t'.image φ.toFun := Finset.mem_image_of_mem _ hxt
        have hρx_s : φ.toFun x ∈ s'.image φ.toFun := heq hρx
        rw [Finset.mem_image] at hρx_s
        obtain ⟨y, hy, hρeq⟩ := hρx_s
        exact hinj hρeq ▸ hy
    exact lab.label_strictMono _ _ (hA'_sub hs'_A') (hA'_sub ht'_A') h_img_ssubset
  have uniq := 𝒜₁.apt_unique_labelling A hA L L
    lab.labelMap (fun s' => lab.labelMap (s'.image φ.toFun))
    hmono1 hmono2 C hCmax
  have hC_fix : C.image φ.toFun = C := by
    ext v; simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      have : φ.toFun w = w := hφ_fix w ⟨C, hCmax.1, hw⟩ ⟨C, hCA', hw⟩
      rw [this]; exact hw
    · intro hv; exact ⟨v, hv, hφ_fix v ⟨C, hCmax.1, hv⟩ ⟨C, hCA', hv⟩⟩
  have h_agree : lab.labelMap (C.image φ.toFun) = (lab.labelMap C).image id := by
    simp [hC_fix]
  intro s hs
  have h_part2 := uniq.2 id Function.bijective_id h_agree s hs
  simp at h_part2
  exact h_part2

/--
[section_4_4_corollary](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma section_4_4_corollary
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {L : Type}
  [DecidableEq L]
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
  {lab : Labelling b.toChamberComplex.toSimplicialComplex L}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  (∃ φ : SimplicialMap A A', (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) ∧ (∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s)) ∧ (∀ (φ : SimplicialMap A A'), Function.Bijective φ.toFun → (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ t ∈ A'.faces, v ∈ t) → φ.toFun v = v) → ∀ s ∈ A.faces, lab.labelMap (s.image φ.toFun) = lab.labelMap s) :=
-- proof
  ⟨cross_system_iso_preserves_labels b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA' lab,
    fun φ hbij hfix =>
      any_iso_fixing_intersection_preserves_labels b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA' lab φ hbij hfix⟩

/--
[cross_system_iso_exists_for_apt_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_iso_exists_for_apt_system
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {x : Finset V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (hxA : x ∈ A.faces)
  (hxA' : x ∈ A'.faces)
  (hCmax : A.IsMaximal C)
  (hCA' : C ∈ A'.faces) :
-- imply
  ∃ φ : SimplicialMap A A', (∀ v ∈ x, φ.toFun v = v) ∧ (∀ v ∈ C, φ.toFun v = v) := by
-- proof
  obtain ⟨φ, _hbij, _hfaces, hfix, hfixC⟩ :=
    cross_system_iso_exists b 𝒜₁ 𝒜₂ A hA A' hA' C hCmax hCA'
  refine ⟨φ, ?_, hfixC⟩
  intro v hv
  exact hfix v ⟨x, hxA, hv⟩ ⟨x, hxA', hv⟩

/--
[cross_system_iso_bijective_for_apt_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma cross_system_iso_bijective_for_apt_system
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜₁ 𝒜₂ : ApartmentSystem b.toChamberComplex}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ 𝒜₁.apartments)
  (hA' : A' ∈ 𝒜₂.apartments)
  (_hCA : C ∈ A.faces)
  (hCA' : C ∈ A'.faces)
  (hCmax : A.IsMaximal C) :
-- imply
  ∃ φ : V → V, Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces) := by
-- proof
  obtain ⟨φ, hbij, hfaces, _⟩ :=
    cross_system_iso_bijective b 𝒜₁ 𝒜₂ A hA A' hA' C _hCA hCA' hCmax
  exact ⟨φ, hbij, hfaces⟩

/--
[apartment_union_is_apartment_system](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma apartment_union_is_apartment_system
  {V : Type}
  [DecidableEq V]
  {b : Building V} :
-- imply
  ∃ 𝒜_max : ApartmentSystem b.toChamberComplex, 𝒜_max.apartments = ⋃ (𝒜 : ApartmentSystem b.toChamberComplex), 𝒜.apartments := by
-- proof
  let K := b.toChamberComplex
  let union_apts := ⋃ (𝒜 : ApartmentSystem K), 𝒜.apartments
  have mem_union_iff : ∀ A, A ∈ union_apts ↔ ∃ 𝒜 : ApartmentSystem K, A ∈ 𝒜.apartments := by
    intro A
    exact Set.mem_iUnion
  refine ⟨⟨union_apts, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, rfl⟩
  · obtain ⟨A, hA⟩ := b.apartmentSystem.nonempty_apartments
    exact ⟨A, (mem_union_iff A).mpr ⟨b.apartmentSystem, hA⟩⟩
  · intro A hA
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.sub A h𝒜
  · intro C D hC hD
    obtain ⟨A, hA, hCA, hDA⟩ := b.apartmentSystem.contains_pair C D hC hD
    exact ⟨A, (mem_union_iff A).mpr ⟨b.apartmentSystem, hA⟩, hCA, hDA⟩
  · intro A hA_union A' hA'_union x hxA hxA' C hCmax hCA'
    obtain ⟨𝒜₁, hA_in⟩ := (mem_union_iff A).mp hA_union
    obtain ⟨𝒜₂, hA'_in⟩ := (mem_union_iff A').mp hA'_union
    exact cross_system_iso_exists_for_apt_system b 𝒜₁ 𝒜₂ A hA_in A' hA'_in x hxA hxA' C hCmax hCA'
  · intro A hA C hCmax
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.maximal_in_apt_is_maximal A h𝒜 C hCmax
  · intro A hA C D hCA hCK hDA hDK g hg hlen E hE
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.gallery_convex A h𝒜 C D hCA hCK hDA hDK g hg hlen E hE
  · intro A hA C hCA hCK
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.building_maximal_in_apt_is_apt_maximal A h𝒜 C hCA hCK
  · intro A hA
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.apt_nonempty A h𝒜
  · intro A hA_union A' hA'_union C hCA hCA' hCmax
    obtain ⟨𝒜₁, hA_in⟩ := (mem_union_iff A).mp hA_union
    obtain ⟨𝒜₂, hA'_in⟩ := (mem_union_iff A').mp hA'_union
    exact cross_system_iso_bijective_for_apt_system b 𝒜₁ 𝒜₂ A hA_in A' hA'_in C hCA hCA' hCmax
  · intro A hA
    obtain ⟨𝒜, h𝒜⟩ := (mem_union_iff A).mp hA
    exact 𝒜.apt_is_coxeter A h𝒜

/--
[apartment_system_subset_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma apartment_system_subset_union
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜_max : ApartmentSystem b.toChamberComplex}
  {𝒜' : ApartmentSystem b.toChamberComplex}
-- given
  (h_max : 𝒜_max.apartments = ⋃ (𝒜 : ApartmentSystem b.toChamberComplex), 𝒜.apartments) :
-- imply
  𝒜'.apartments ⊆ 𝒜_max.apartments := by
-- proof
  rw [h_max]
  exact Set.subset_iUnion (fun 𝒜 => 𝒜.apartments) 𝒜'

/--
[apartment_system_maximal_unique](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/MaximalApartments.lean)
-/
@[path]
lemma apartment_system_maximal_unique
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {𝒜_max : ApartmentSystem b.toChamberComplex}
  {𝒜' : ApartmentSystem b.toChamberComplex}
-- given
  (h_max : 𝒜_max.apartments = ⋃ (𝒜 : ApartmentSystem b.toChamberComplex), 𝒜.apartments)
  (h_all : ∀ 𝒜'' : ApartmentSystem b.toChamberComplex, 𝒜''.apartments ⊆ 𝒜'.apartments) :
-- imply
  𝒜_max.apartments = 𝒜'.apartments := by
-- proof
  apply Set.Subset.antisymm
  ·
    rw [h_max]
    intro A hA
    rw [Set.mem_iUnion] at hA
    obtain ⟨𝒜'', h𝒜''⟩ := hA
    exact h_all 𝒜'' h𝒜''
  ·
    exact apartment_system_subset_union b 𝒜_max h_max 𝒜'


-- created on 2026-10-23
