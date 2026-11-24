module
public import Mathlib
public import Def.WeierstrassCurve_TateModule
public import Instance.PDivisibleGroup_PrimaryTorsion
set_option autoImplicit false


public section

def PrimaryTorsion (p : ℕ) (M : Type) [AddCommGroup M] : AddSubgroup M :=
  AddCommGroup.primaryComponent M p

namespace PrimaryTorsion

variable {p : ℕ} {M : Type} [AddCommGroup M]


section Map

variable {N : Type} [AddCommGroup N]

variable [Fact p.Prime]

noncomputable def map (f : M →+ N) : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p N where
  toFun x := ⟨f x, map_mem f x⟩
  map_add' x y := Subtype.ext (by
    change f ((x + y : PrimaryTorsion p M) : M) = f x + f y
    rw [AddSubgroup.coe_add, map_add])
  map_smul' a x := Subtype.ext (by
    obtain ⟨k, hk⟩ := x.2
    have hfk : p ^ k • ((⟨f x, map_mem f x⟩ : PrimaryTorsion p N) : N) = 0 := by
      change p ^ k • f x = 0
      rw [← map_nsmul, hk, map_zero]
    change f ((a • x : PrimaryTorsion p M) : M) = ((a • (⟨f x, map_mem f x⟩ : PrimaryTorsion p N) :
      PrimaryTorsion p N) : N)
    rw [coe_smul a x hk, coe_smul a _ hfk, map_zsmul])

end Map

section Tate

variable (p M) [Fact p.Prime]

noncomputable def ofTateModule (n : ℕ) : TateModule p M →ₗ[ℤ_[p]] PrimaryTorsion p M where
  toFun x := ⟨(x : ℕ → M) n, mem_of_mem_torsionBy (TateModule.proj_mem_torsionBy n x)⟩
  map_add' _ _ := rfl
  map_smul' a x := Subtype.ext (by
    have hn : p ^ n • (x : ℕ → M) n = 0 := by
      rw [← natCast_zsmul]; exact TateModule.torsion x n
    change ((a • x : TateModule p M) : ℕ → M) n =
      ((a • (⟨(x : ℕ → M) n, mem_of_mem_torsionBy (TateModule.proj_mem_torsionBy n x)⟩ : PrimaryTorsion p M) :
        PrimaryTorsion p M) : M)
    rw [TateModule.smul_apply, coe_smul a _ hn])

variable {p M}

end Tate

end PrimaryTorsion
