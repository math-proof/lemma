import Mathlib

set_option autoImplicit false

namespace ValuationSubring

open IsLocalRing

variable {L : Type*} [Field L]

noncomputable def residueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    ValuationSubring (ResidueField S) :=
  ValuationSubring.ofSubring ((residue S).comp (A.inclusion S h)).range <| by
    intro x
    obtain ⟨s, rfl⟩ := residue_surjective x
    rcases A.mem_or_inv_mem (s : L) with hs | hs
    · exact Or.inl ⟨⟨s, hs⟩, rfl⟩
    · by_cases hu : IsUnit s
      · obtain ⟨u, rfl⟩ := hu
        have hinv : (((u⁻¹ : Sˣ) : S) : L) = ((u : S) : L)⁻¹ := map_units_inv S.subtype u
        refine Or.inr ⟨⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩, ?_⟩
        change residue S (A.inclusion S h ⟨((u⁻¹ : Sˣ) : S), hinv ▸ hs⟩) = (residue S u)⁻¹
        rw [← map_units_inv]
        rfl
      · refine Or.inl ⟨0, ?_⟩
        rw [map_zero, eq_comm, residue_eq_zero_iff]
        exact (_root_.mem_nonunits_iff.mpr hu)

noncomputable def toResidueValuationSubring (A S : ValuationSubring L) (h : A ≤ S) :
    A →+* A.residueValuationSubring S h :=
  ((residue S).comp (A.inclusion S h)).codRestrict (A.residueValuationSubring S h) fun a => ⟨a, rfl⟩

variable (A S : ValuationSubring L) (h : A ≤ S)

theorem mem_residueValuationSubring_iff {x : ResidueField S} :
    x ∈ A.residueValuationSubring S h ↔ ∃ a : A, residue S (A.inclusion S h a) = x :=
  Iff.rfl

@[simp]
theorem coe_toResidueValuationSubring (a : A) :
    (A.toResidueValuationSubring S h a : ResidueField S) = residue S (A.inclusion S h a) :=
  rfl

theorem toResidueValuationSubring_surjective :
    Function.Surjective (A.toResidueValuationSubring S h) := by
  rintro ⟨x, a, rfl⟩
  exact ⟨a, rfl⟩

theorem ker_toResidueValuationSubring :
    RingHom.ker (A.toResidueValuationSubring S h) = A.idealOfLE S h := by
  ext a
  rw [RingHom.mem_ker, ← Subtype.coe_inj, coe_toResidueValuationSubring, ZeroMemClass.coe_zero,
    residue_eq_zero_iff]
  rfl

end ValuationSubring
