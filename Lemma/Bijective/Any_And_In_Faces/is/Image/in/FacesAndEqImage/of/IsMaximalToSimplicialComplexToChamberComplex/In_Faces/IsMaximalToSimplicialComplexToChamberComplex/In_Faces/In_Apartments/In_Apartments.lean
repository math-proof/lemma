import Mathlib
import sympy.Basic
import Theorem.v1.Atlas.Buildings.code.Building.UniqueRetraction
open scoped Classical


/--
[apartment_iso_sending_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
lemma apartment_iso_sending_chamber
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {B : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hB : B ∈ b.apartmentSystem.apartments)
  (hC_A : C ∈ A.faces)
  (hC_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hD_B : D ∈ B.faces)
  (hD_max_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ B.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  obtain ⟨A₀, hA₀, hC_A₀, hD_A₀⟩ :=
    b.apartmentSystem.contains_pair C D hC_max_bldg hD_max_bldg
  have hD_max_B : B.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max_bldg
  have hD_max_A₀ : A₀.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A₀ hA₀ D hD_A₀ hD_max_bldg
  have hC_max_A₀ : A₀.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A₀ hA₀ C hC_A₀ hC_max_bldg
  have hC_max_A : A.IsMaximal C :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A hA C hC_A hC_max_bldg
  obtain ⟨φ₁, hφ₁_bij, hφ₁_faces⟩ :=
    b.apartmentSystem.iso_bijective B hB A₀ hA₀ D hD_B hD_A₀ hD_max_B
  obtain ⟨φ₂, hφ₂_bij, hφ₂_faces⟩ :=
    b.apartmentSystem.iso_bijective A₀ hA₀ A hA C hC_A₀ hC_A hC_max_A₀
  set φ₀ := φ₂ ∘ φ₁
  have hφ₀_bij : Function.Bijective φ₀ := hφ₂_bij.comp hφ₁_bij
  have hφ₀_faces : ∀ s, s ∈ B.faces ↔ s.image φ₀ ∈ A.faces := by
    intro s
    simp only [φ₀, ← Finset.image_image]
    exact Iff.trans (hφ₁_faces s) (hφ₂_faces (s.image φ₁))
  set E := D.image φ₀ with hE_def
  have hE_A : E ∈ A.faces := (hφ₀_faces D).mp hD_B
  have hD_img_max_A₀ : A₀.IsMaximal (D.image φ₁) :=
    bijective_face_iso_preserves_maximal hφ₁_bij hφ₁_faces hD_max_B
  have hE_max_A : A.IsMaximal E := by
    rw [hE_def, show D.image φ₀ = (D.image φ₁).image φ₂ from by simp [φ₀, Finset.image_image]]
    exact bijective_face_iso_preserves_maximal hφ₂_bij hφ₂_faces hD_img_max_A₀
  obtain ⟨α, hα_bij, hα_faces, hα_EC⟩ :=
    apt_automorphism_sending_chamber b A hA C hC_max_A E hE_max_A
  refine ⟨α ∘ φ₀, hα_bij.comp hφ₀_bij, ?_, ?_⟩
  ·
    intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hφ₀_faces s) (hα_faces (s.image φ₀))
  ·
    simp only [← Finset.image_image]
    exact hα_EC

/--
[bij_iso_fixing_chamber_is_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
lemma bij_iso_fixing_chamber_is_id
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {B B' : SimplicialComplex V}
  {D : Finset V}
  {φ : V → V}
-- given
  (hB : B ∈ b.apartmentSystem.apartments)
  (hD_B : D ∈ B.faces)
  (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D)
  (hφ_bij : Function.Bijective φ)
  (_hφ_faces : ∀ s, s ∈ B.faces ↔ s.image φ ∈ B'.faces)
  (hφ_D : D.image φ = D) :
-- imply
  ∀ s ∈ B.faces, s.image φ = s := by
-- proof
  have hD_max_B : B.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
  have hmono_id : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t → s ⊂ t := by
    intro s t _ _ h; exact h
  have hmono_φ : ∀ s t, s ∈ B.faces → t ∈ B.faces → s ⊂ t →
    s.image φ ⊂ t.image φ := by
    intro s t _ _ hst
    exact finset_image_ssubset_of_injective hφ_bij.1 hst
  obtain ⟨_, hprop⟩ := b.apartmentSystem.apt_unique_labelling B hB
    V V id (fun s => s.image φ) hmono_id hmono_φ D hD_max_B
  have h_agree_D : D.image φ = (id D).image (id : V → V) := by
    simp [hφ_D]
  intro s hs
  have := hprop id Function.bijective_id h_agree_D s hs
  simp at this
  exact this

/--
[iso_bijective_fixing_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
lemma iso_bijective_fixing_chamber
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {B : SimplicialComplex V}
  {B₀ : SimplicialComplex V}
  {D : Finset V}
-- given
  (hB : B ∈ b.apartmentSystem.apartments)
  (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
  (hD_B : D ∈ B.faces)
  (hD_B₀ : D ∈ B₀.faces)
  (hD_max_B : B.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ B.faces ↔ s.image φ ∈ B₀.faces) ∧ D.image φ = D := by
-- proof
  obtain ⟨ψ, hψ_bij, hψ_faces⟩ :=
    b.apartmentSystem.iso_bijective B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
  have hDψ_max_B₀ : B₀.IsMaximal (D.image ψ) :=
    bijective_face_iso_preserves_maximal hψ_bij hψ_faces hD_max_B
  have hD_max_B₀ : B₀.IsMaximal D :=
    b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀
      (b.apartmentSystem.maximal_in_apt_is_maximal B hB D hD_max_B)
  obtain ⟨α, hα_bij, hα_faces, hα_send⟩ :=
    apt_automorphism_sending_chamber b B₀ hB₀ D hD_max_B₀ (D.image ψ) hDψ_max_B₀
  refine ⟨α ∘ ψ, hα_bij.comp hψ_bij, ?_, ?_⟩
  ·
    intro s
    simp only [← Finset.image_image]
    exact Iff.trans (hψ_faces s) (hα_faces (s.image ψ))
  ·
    simp only [← Finset.image_image]
    exact hα_send

/--
[exists_canonical_retraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
lemma exists_canonical_retraction
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {B₀ : SimplicialComplex V}
  {D : Finset V}
-- given
  (hB₀ : B₀ ∈ b.apartmentSystem.apartments)
  (hD_B₀ : D ∈ B₀.faces)
  (hD_max : b.toChamberComplex.toSimplicialComplex.IsMaximal D) :
-- imply
  ∃ (ρ : V → V), (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ ∈ B₀.faces) ∧ (∀ v, (∃ s ∈ B₀.faces, v ∈ s) → ρ v = v) ∧ (D.image ρ = D) ∧ (∀ B ∈ b.apartmentSystem.apartments, D ∈ B.faces → Function.Injective (fun v : V => ρ v) ∧ (∀ s, s ∈ B.faces ↔ s.image ρ ∈ B₀.faces)) ∧ (∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces, s.image ρ = s) := by
-- proof
  have apt_faces_sub : ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
    D ∈ B.faces → B.faces ⊆ B₀.faces := by
    intro B hB hD_B s hs
    have hD_max_B : B.IsMaximal D :=
      b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B hB D hD_B hD_max
    obtain ⟨φ, hφ_bij, hφ_faces, hφ_D⟩ :=
      iso_bijective_fixing_chamber b B hB B₀ hB₀ D hD_B hD_B₀ hD_max_B
    have hid := bij_iso_fixing_chamber_is_id b B B₀ hB D hD_B hD_max φ hφ_bij hφ_faces hφ_D s hs
    rw [← hid]
    exact (hφ_faces s).mp hs
  have apt_faces_sup : ∀ (B : SimplicialComplex V), B ∈ b.apartmentSystem.apartments →
    D ∈ B.faces → B₀.faces ⊆ B.faces := by
    intro B hB hD_B s hs
    have hD_max_B₀ : B₀.IsMaximal D :=
      b.apartmentSystem.building_maximal_in_apt_is_apt_maximal B₀ hB₀ D hD_B₀ hD_max
    obtain ⟨ψ, hψ_bij, hψ_faces, hψ_D⟩ :=
      iso_bijective_fixing_chamber b B₀ hB₀ B hB D hD_B₀ hD_B hD_max_B₀
    have hid := bij_iso_fixing_chamber_is_id b B₀ B hB₀ D hD_B₀ hD_max ψ hψ_bij hψ_faces hψ_D s hs
    rw [← hid]
    exact (hψ_faces s).mp hs
  have all_faces_in_B₀ : ∀ s ∈ b.toChamberComplex.toSimplicialComplex.faces,
    s ∈ B₀.faces := by
    intro s hs
    obtain ⟨E, hE_max, hs_sub⟩ := b.toChamberComplex.exists_maximal s hs
    obtain ⟨B, hB, hD_B, hE_B⟩ := b.apartmentSystem.contains_pair D E hD_max hE_max
    have hs_B : s ∈ B.faces :=
      B.down_closed hE_B hs_sub (b.toChamberComplex.toSimplicialComplex.nonempty_of_mem s hs)
    exact apt_faces_sub B hB hD_B hs_B
  refine ⟨id, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro s hs
    simp
    exact all_faces_in_B₀ s hs
  ·
    intro v _
    rfl
  ·
    simp
  ·
    intro B hB hD_B
    constructor
    ·
      exact Function.injective_id
    ·
      intro s
      simp
      exact ⟨fun h => apt_faces_sub B hB hD_B h, fun h => apt_faces_sup B hB hD_B h⟩
  ·
    intro s _
    simp
/-- Uniqueness of the retraction $\rho_{D;C,A}$: any two retractions onto
$A$ centered at $C$ with the same chamber-level behaviour agree (Section
15.5). -/

/--
[finset_image_ssubset_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
private lemma finset_image_ssubset_of_injective_eq
  {V : Type}
  [DecidableEq V]
  {f : V → V}
  {s t : Finset V}
-- given
  (hf : Function.Injective f)
  (h : s ⊂ t) :
-- imply
  s.image f ⊂ t.image f := by
-- proof
  apply finset_image_ssubset_of_injective hf h

/--
[apt_automorphism_sending_chamber](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
private lemma apt_automorphism_sending_chamber_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A : SimplicialComplex V}
  {C : Finset V}
  {D : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hD : A.IsMaximal D) :
-- imply
  ∃ (φ : V → V), Function.Bijective φ ∧ (∀ s, s ∈ A.faces ↔ s.image φ ∈ A.faces) ∧ D.image φ = C := by
-- proof
  apply apt_automorphism_sending_chamber b A hA C hC D hD

/--
[bijective_face_iso_preserves_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/UniqueRetraction.lean)
-/
@[path]
private lemma bijective_face_iso_preserves_maximal_eq
  {V : Type}
  [DecidableEq V]
  {A A' : SimplicialComplex V}
  {φ : V → V}
  {s : Finset V}
-- given
  (hφ_bij : Function.Bijective φ)
  (hφ_faces : ∀ s, s ∈ A.faces ↔ s.image φ ∈ A'.faces)
  (hs : A.IsMaximal s) :
-- imply
  A'.IsMaximal (s.image φ) := by
-- proof
  apply bijective_face_iso_preserves_maximal hφ_bij hφ_faces hs


-- created on 2026-10-23
