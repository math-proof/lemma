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

end ValuationSubring
