import Mathlib
import Def.ValuationSubring_ResidueValuationSubring

set_option autoImplicit false

namespace ValuationSubring

open IsLocalRing

variable {L : Type*} [Field L]


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
