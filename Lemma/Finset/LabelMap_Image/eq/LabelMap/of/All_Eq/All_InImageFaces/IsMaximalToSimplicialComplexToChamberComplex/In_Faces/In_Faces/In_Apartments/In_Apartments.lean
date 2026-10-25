import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.LabelPreservingIso
open scoped Classical


/--
[apt_iso_fixing_intersection_is_label_preserving](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/LabelPreservingIso.lean)
-/
@[path]
lemma apt_iso_fixing_intersection_is_label_preserving
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A A' : SimplicialComplex V}
  {C : Finset V}
  {φ : V → V}
  {L : Type}
  [DecidableEq L]
  {lab : Labelling b.toChamberComplex.toSimplicialComplex L}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hA' : A' ∈ b.apartmentSystem.apartments)
  (hC_A : C ∈ A.faces)
  (hC_A' : C ∈ A'.faces)
  (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (_hφ_face : ∀ s ∈ A.faces, s.image φ ∈ A'.faces)
  (hφ_fixes : ∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) :
-- imply
  ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s := by
-- proof
  have hA'_sub_A : A'.faces ⊆ A.faces :=
    apt_faces_subset b A A' hA hA' C hC_A hC_A' hC_max
  have hA_sub_A' : A.faces ⊆ A'.faces :=
    apt_faces_subset b A' A hA' hA C hC_A' hC_A hC_max
  have hφ_id : ∀ v, (∃ s ∈ A.faces, v ∈ s) → φ v = v := by
    intro v hv
    apply hφ_fixes v hv
    obtain ⟨s, hs, hvs⟩ := hv
    exact ⟨s, hA_sub_A' hs, hvs⟩
  intro s hs
  have : s.image φ = s := by
    ext v; simp only [Finset.mem_image]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [hφ_id w ⟨s, hs, hw⟩]; exact hw
    · intro hv; exact ⟨v, hv, hφ_id v ⟨s, hs, hv⟩⟩
  rw [this]

private lemma apt_iso_label_preserving
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {A A' : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hA' : A' ∈ b.apartmentSystem.apartments)
  (hC_A : C ∈ A.faces)
  (hC_A' : C ∈ A'.faces)
  (hC_max : b.toChamberComplex.toSimplicialComplex.IsMaximal C) :
-- imply
  (∃ (φ : V → V), (∀ s ∈ A.faces, s.image φ ∈ A'.faces) ∧ (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) ∧ Function.Bijective φ ∧ ∀ (L : Type) [DecidableEq L] (lab : Labelling b.toChamberComplex.toSimplicialComplex L), ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s) ∧ (∀ (φ : V → V), (∀ s ∈ A.faces, s.image φ ∈ A'.faces) → (∀ v, (∃ s ∈ A.faces, v ∈ s) → (∃ s ∈ A'.faces, v ∈ s) → φ v = v) → ∀ (L : Type) [DecidableEq L] (lab : Labelling b.toChamberComplex.toSimplicialComplex L), ∀ s ∈ A.faces, lab.labelMap (s.image φ) = lab.labelMap s) := by
-- proof
  constructor
  ·
    obtain ⟨φ, hφ_face, hφ_fixes, hφ_bij⟩ :=
      apt_iso_exists_fixing_intersection b A A' hA hA' C hC_A hC_A' hC_max
    have hφ_fwd : ∀ s ∈ A.faces, s.image φ ∈ A'.faces := fun s hs => (hφ_face s).mp hs
    exact ⟨φ, hφ_fwd, hφ_fixes, hφ_bij,
      fun L _ lab => apt_iso_fixing_intersection_is_label_preserving
        b A A' hA hA' C hC_A hC_A' hC_max φ hφ_fwd hφ_fixes L lab⟩
  ·
    intro φ hφ_face hφ_fixes L _ lab
    exact apt_iso_fixing_intersection_is_label_preserving
      b A A' hA hA' C hC_A hC_A' hC_max φ hφ_face hφ_fixes L lab


-- created on 2026-10-24
