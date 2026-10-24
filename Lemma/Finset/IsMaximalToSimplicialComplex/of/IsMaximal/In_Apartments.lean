import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.Building.ApartmentsCoxeter
open ChamberComplex Building


/--
[apartment_chamber_is_building_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/ApartmentsCoxeter.lean)
-/
@[path]
lemma apartment_chamber_is_building_chamber
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hCmax : A.IsMaximal C) :
-- imply
  b.toSimplicialComplex.IsMaximal C :=
-- proof
  b.apartmentSystem.maximal_in_apt_is_maximal A hA C hCmax


private lemma building_chamber_in_apartment_is_apartment_chamber
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_in_A : C ∈ A.faces)
  (hCmax : b.toSimplicialComplex.IsMaximal C) :
-- imply
  A.IsMaximal C :=
-- proof
  b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_in_A hCmax


private lemma apartment_has_chamber
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments) :
-- imply
  ∃ C : Finset V, C ∈ A.faces ∧ A.IsMaximal C := by
-- proof
  obtain ⟨_, _, cc, hcc_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA
  obtain ⟨s, hs⟩ := b.apartmentSystem.apt_nonempty A hA
  have hs_cc : s ∈ cc.toSimplicialComplex.faces := hcc_eq ▸ hs
  obtain ⟨C, hCmax_cc, _⟩ := cc.exists_maximal s hs_cc
  have hCmax_A : A.IsMaximal C := hcc_eq ▸ hCmax_cc
  exact ⟨C, hCmax_A.1, hCmax_A⟩


private lemma iso_exists_gives_iso
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hA' : A' ∈ b.apartmentSystem.apartments)
  (hCA : C ∈ A.faces)
  (hCA' : C ∈ A'.faces)
  (hCmax : A.IsMaximal C) :
-- imply
  SimplicialComplexIso A A' :=
-- proof
  b.apartmentSystem.iso_bijective A hA A' hA' C hCA hCA' hCmax


private lemma simplicialComplexIso_trans
  [DecidableEq V] :
-- imply
  ∀ (A B A' : SimplicialComplex V), SimplicialComplexIso A B → SimplicialComplexIso B A' → SimplicialComplexIso A A' := by
-- proof
  intro A B A' ⟨φ, hφ_bij, hφ_face⟩ ⟨ψ, hψ_bij, hψ_face⟩
  refine ⟨ψ ∘ φ, hψ_bij.comp hφ_bij, fun s => ?_⟩
  simp only [← Finset.image_image]
  exact (hφ_face s).trans (hψ_face _)


private lemma AllApartmentsIsomorphic
  [DecidableEq V]
  {b : Building V} :
-- imply
  ∀ A ∈ b.apartmentSystem.apartments, ∀ A' ∈ b.apartmentSystem.apartments, SimplicialComplexIso A A' := by
-- proof
  intro A hA A' hA'
  obtain ⟨C, hCA, hCmaxA⟩ := apartment_has_chamber b A hA
  obtain ⟨C', hC'A', hC'maxA'⟩ := apartment_has_chamber b A' hA'
  have hCmax_bldg := apartment_chamber_is_building_chamber b A hA C hCmaxA
  have hC'max_bldg := apartment_chamber_is_building_chamber b A' hA' C' hC'maxA'
  obtain ⟨B, hB, hCB, hC'B⟩ := b.apartmentSystem.contains_pair C C' hCmax_bldg hC'max_bldg
  have hCmaxB := building_chamber_in_apartment_is_apartment_chamber b B hB C hCB hCmax_bldg
  have hC'maxB := building_chamber_in_apartment_is_apartment_chamber b B hB C' hC'B hC'max_bldg
  have hAB : SimplicialComplexIso A B :=
    iso_exists_gives_iso b A hA B hB C hCA hCB hCmaxA
  have hBA' : SimplicialComplexIso B A' :=
    iso_exists_gives_iso b B hB A' hA' C' hC'B hC'A' hC'maxB
  exact simplicialComplexIso_trans A B A' hAB hBA'


private lemma apartment_is_coxeter_complex
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments) :
-- imply
  ∃ (B_idx : Type) (M : CoxeterMatrix B_idx) (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ ∃ (φ : Finset V → M.Group), (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧ (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧ (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) ∧ cc.IsThin :=
-- proof
  b.apartmentSystem.apt_is_coxeter A hA


private lemma finset_image_sdiff_of_inj
  [DecidableEq V]
  [DecidableEq α]
  [DecidableEq β]
  {f : α → β}
  {s t : Finset α}
-- given
  (hf : Function.Injective f)
  (_hts : t ⊆ s) :
-- imply
  (s \ t).image f = s.image f \ t.image f := by
-- proof
  ext b
  simp only [Finset.mem_image, Finset.mem_sdiff]
  constructor
  · rintro ⟨a, ⟨has, hat⟩, rfl⟩
    exact ⟨⟨a, has, rfl⟩, fun ⟨a', ha't, hfa'⟩ => hat (hf hfa' ▸ ha't)⟩
  · rintro ⟨⟨a, has, rfl⟩, hnot⟩
    exact ⟨a, ⟨has, fun hat => hnot ⟨a, hat, rfl⟩⟩, rfl⟩


private lemma image_inv_image_eq
  [DecidableEq V]
  {φ inv : V → V}
  {s : Finset V}
-- given
  (hright : ∀ v, φ (inv v) = v) :
-- imply
  (s.image inv).image φ = s := by
-- proof
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; rwa [hright]
  · intro hv; exact ⟨inv v, ⟨v, hv, rfl⟩, hright v⟩


private lemma image_phi_image_eq
  [DecidableEq V]
  {φ inv : V → V}
  {s : Finset V}
-- given
  (hleft : ∀ v, inv (φ v) = v) :
-- imply
  (s.image φ).image inv = s := by
-- proof
  ext v; simp only [Finset.mem_image]
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; rwa [hleft]
  · intro hv; exact ⟨φ v, ⟨v, hv, rfl⟩, hleft v⟩


private lemma iso_pullback_maximal
  [DecidableEq V]
  {A₀ A : SimplicialComplex V}
  {φ inv : V → V}
  {C : Finset V}
-- given
  (hright : ∀ v, φ (inv v) = v)
  (hleft : ∀ v, inv (φ v) = v)
  (hφ_face : ∀ s, s ∈ A₀.faces ↔ s.image φ ∈ A.faces)
  (hCmax : A.IsMaximal C) :
-- imply
  A₀.IsMaximal (C.image inv) := by
-- proof
  constructor
  · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hCmax.1
  · intro y hy hsub
    have hy_A : y.image φ ∈ A.faces := (hφ_face y).mp hy
    have hsub' : C ⊆ y.image φ := by
      rw [← image_inv_image_eq hright C]
      exact Finset.image_subset_image hsub
    have := hCmax.2 _ hy_A hsub'
    rw [this]; exact image_phi_image_eq hleft y


private lemma iso_preserves_coxeter_type
  [DecidableEq V]
  {b : Building V}
  {A₀ : SimplicialComplex V}
  {B_idx : Type}
  {M : CoxeterMatrix B_idx}
  {cc₀ : ChamberComplex V}
  {φ₀ : Finset V → M.Group}
  {A : SimplicialComplex V}
-- given
  (_hA₀ : A₀ ∈ b.apartmentSystem.apartments)
  (_hcc₀ : cc₀.toSimplicialComplex = A₀)
  (hinj₀ : ∀ C, A₀.IsMaximal C → ∀ D, A₀.IsMaximal D → φ₀ C = φ₀ D → C = D)
  (hsurj₀ : ∀ w : M.Group, ∃ C, A₀.IsMaximal C ∧ φ₀ C = w)
  (hadj₀ : ∀ C C', A₀.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ₀ C) (φ₀ C'))
  (hA : A ∈ b.apartmentSystem.apartments)
  (hiso : SimplicialComplexIso A₀ A) :
-- imply
  ∃ (cc : ChamberComplex V), cc.toSimplicialComplex = A ∧ ∃ (φ : Finset V → M.Group), (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧ (∀ w : M.Group, ∃ C, A.IsMaximal C ∧ φ C = w) ∧ (∀ C C', A.Adjacent C C' → CoxeterComplex.ChamberAdjacent M (φ C) (φ C')) := by
-- proof
  obtain ⟨_, _, ccA, hccA_eq, _⟩ := b.apartmentSystem.apt_is_coxeter A hA
  obtain ⟨φ_iso, hφ_bij, hφ_face⟩ := hiso
  have hφ_surj := hφ_bij.2
  let inv := Function.surjInv hφ_surj
  have hright : ∀ v, φ_iso (inv v) = v := Function.surjInv_eq hφ_surj
  have hleft : ∀ v, inv (φ_iso v) = v := fun v => hφ_bij.1 (hright (φ_iso v))
  have hinv_inj : Function.Injective inv := fun a b h => by
    have := congr_arg φ_iso h; rwa [hright, hright] at this
  refine ⟨ccA, hccA_eq, fun C => φ₀ (C.image inv), ?_, ?_, ?_⟩
  ·
    intro C hCmax D hDmax heq
    have hC_inv_max := iso_pullback_maximal hright hleft hφ_face C hCmax
    have hD_inv_max := iso_pullback_maximal hright hleft hφ_face D hDmax
    have := hinj₀ _ hC_inv_max _ hD_inv_max heq
    have h1 : (C.image inv).image φ_iso = (D.image inv).image φ_iso := by rw [this]
    rwa [image_inv_image_eq hright, image_inv_image_eq hright] at h1
  ·
    intro w
    obtain ⟨C₀, hC₀max, hC₀w⟩ := hsurj₀ w
    refine ⟨C₀.image φ_iso, ?_, ?_⟩
    ·
      constructor
      · exact (hφ_face C₀).mp hC₀max.1
      · intro y hy hsub
        have hy_A₀ : y.image inv ∈ A₀.faces := by
          rw [hφ_face]; rwa [image_inv_image_eq hright]
        have hsub' : C₀ ⊆ y.image inv := by
          rw [← image_phi_image_eq hleft C₀]
          exact Finset.image_subset_image hsub
        have h := hC₀max.2 _ hy_A₀ hsub'
        rw [← image_inv_image_eq hright y, ← h]
    ·
      show φ₀ ((C₀.image φ_iso).image inv) = w
      rw [image_phi_image_eq hleft, hC₀w]
  ·
    intro C C' hadj_A
    obtain ⟨hCmax, hC'max, hne, F, hFC, hFC'⟩ := hadj_A
    have hC_inv_max := iso_pullback_maximal hright hleft hφ_face C hCmax
    have hC'_inv_max := iso_pullback_maximal hright hleft hφ_face C' hC'max
    have hne_inv : C.image inv ≠ C'.image inv := by
      intro h
      apply hne
      have := congr_arg (Finset.image φ_iso) h
      rwa [image_inv_image_eq hright, image_inv_image_eq hright] at this
    have hF_inv_face_C : A₀.IsFacet (F.image inv) (C.image inv) := by
      refine ⟨⟨?_, ?_, Finset.image_subset_image hFC.1.2.2⟩, ?_⟩
      · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hFC.1.1
      · exact hC_inv_max.1
      · rw [← finset_image_sdiff_of_inj hinv_inj C F hFC.1.2.2,
        Finset.card_image_of_injective _ hinv_inj]
        exact hFC.2
    have hF_inv_face_C' : A₀.IsFacet (F.image inv) (C'.image inv) := by
      refine ⟨⟨?_, ?_, Finset.image_subset_image hFC'.1.2.2⟩, ?_⟩
      · rw [hφ_face]; rw [image_inv_image_eq hright]; exact hFC'.1.1
      · exact hC'_inv_max.1
      · rw [← finset_image_sdiff_of_inj hinv_inj C' F hFC'.1.2.2,
        Finset.card_image_of_injective _ hinv_inj]
        exact hFC'.2
    exact hadj₀ _ _ ⟨hC_inv_max, hC'_inv_max, hne_inv,
      F.image inv, hF_inv_face_C, hF_inv_face_C'⟩


-- created on 2026-10-24
