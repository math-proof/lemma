-- Carved from Lemma/Definitions/Def_PDivisibleGroup_PrimaryTorsion.lean: instance decls only.
import Mathlib
import Instance.EllipticCurve_TateModule
import Lemma.PDivisibleGroup.PrimaryTorsion

set_option autoImplicit false

namespace PrimaryTorsion

variable {p : ℕ} {M : Type} [AddCommGroup M]

section Module

variable [Fact p.Prime]

noncomputable instance instSMul : SMul ℤ_[p] (PrimaryTorsion p M) :=
  ⟨fun a x => ⟨((a.appr (Classical.choose x.2) : ℕ) : ℤ) • (x : M), AddSubgroup.zsmul_mem _ x.2 _⟩⟩

noncomputable instance instModule : Module ℤ_[p] (PrimaryTorsion p M) where
  one_smul x := by
    have h := natCast_smul_eq_nsmul 1 x
    rwa [Nat.cast_one, one_nsmul] at h
  mul_smul a b x := by
    obtain ⟨k, hk⟩ := x.2
    have hbx : p ^ k • ((b • x : PrimaryTorsion p M) : M) = 0 := by
      rw [coe_smul b x hk, smul_comm, hk, smul_zero]
    refine Subtype.ext ?_
    rw [coe_smul _ x hk, coe_smul _ _ hbx, coe_smul b x hk, smul_smul, ← Nat.cast_mul]
    refine natCast_zsmul_eq_of_zmod_eq hk ?_
    rw [← TateModule.toZModPow_eq_appr, map_mul, TateModule.toZModPow_eq_appr,
      TateModule.toZModPow_eq_appr, Nat.cast_mul]
  smul_zero a := Subtype.ext (by
    rw [coe_smul a 0 (k := 0) (by rw [pow_zero, one_nsmul]; rfl)]
    exact smul_zero _)
  smul_add a x y := by
    obtain ⟨k, hk⟩ := x.2
    obtain ⟨l, hl⟩ := y.2
    have hk' : p ^ (k + l) • (x : M) = 0 := nsmul_eq_zero_of_le (Nat.le_add_right k l) hk
    have hl' : p ^ (k + l) • (y : M) = 0 := nsmul_eq_zero_of_le (Nat.le_add_left l k) hl
    have hxy : p ^ (k + l) • ((x + y : PrimaryTorsion p M) : M) = 0 := by
      rw [AddSubgroup.coe_add, nsmul_add, hk', hl', add_zero]
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_add, coe_smul a _ hxy, coe_smul a x hk', coe_smul a y hl', AddSubgroup.coe_add,
      smul_add]
  add_smul a b x := by
    obtain ⟨k, hk⟩ := x.2
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_add, coe_smul _ x hk, coe_smul a x hk, coe_smul b x hk, ← add_smul, ← Nat.cast_add]
    refine natCast_zsmul_eq_of_zmod_eq hk ?_
    rw [← TateModule.toZModPow_eq_appr, map_add, TateModule.toZModPow_eq_appr,
      TateModule.toZModPow_eq_appr, Nat.cast_add]
  zero_smul x := by
    have h := natCast_smul_eq_nsmul 0 x
    rwa [Nat.cast_zero, zero_nsmul] at h

end Module


end PrimaryTorsion
