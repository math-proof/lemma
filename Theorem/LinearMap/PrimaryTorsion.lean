module

public import Mathlib
public import Theorem.WeierstrassCurve.TateModule
public import Instance.PDivisibleGroup_PrimaryTorsion

public section

set_option autoImplicit false


public theorem eq_primaryComponent : PrimaryTorsion p M = AddCommGroup.primaryComponent M p := rfl


public theorem mem_iff {x : M} : x ∈ PrimaryTorsion p M ↔ ∃ k : ℕ, p ^ k • x = 0 := Iff.rfl


public theorem mem_of_nsmul_eq_zero {x : M} {k : ℕ} (hx : p ^ k • x = 0) : x ∈ PrimaryTorsion p M := ⟨k, hx⟩


public theorem exists_nsmul_eq_zero (x : PrimaryTorsion p M) : ∃ k : ℕ, p ^ k • (x : M) = 0 := x.2


public theorem mem_of_mem_torsionBy {n : ℕ} {x : M} (hx : x ∈ Submodule.torsionBy ℤ M ((p ^ n : ℕ) : ℤ)) :
    x ∈ PrimaryTorsion p M :=
  ⟨n, by rwa [Submodule.mem_torsionBy_iff, natCast_zsmul] at hx⟩


public theorem nsmul_eq_zero_of_le {x : M} {k l : ℕ} (hkl : k ≤ l) (hx : p ^ k • x = 0) : p ^ l • x = 0 := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le hkl
  rw [pow_add, mul_comm, mul_nsmul', hx, nsmul_zero]


public theorem natCast_zsmul_eq_of_zmod_eq {x : M} {k c d : ℕ} (hx : p ^ k • x = 0)
    (h : (c : ZMod (p ^ k)) = d) : (c : ℤ) • x = (d : ℤ) • x :=
  TateModule.natCast_smul_eq_of_zmod_eq (p := p) (by rw [natCast_zsmul]; exact hx) h

section Module

variable [Fact p.Prime]


public theorem appr_zsmul_eq_appr_zsmul (a : ℤ_[p]) {x : M} {k l : ℕ} (hk : p ^ k • x = 0) (hl : p ^ l • x = 0) :
    ((a.appr k : ℕ) : ℤ) • x = ((a.appr l : ℕ) : ℤ) • x := by
  wlog hkl : k ≤ l generalizing k l
  · exact (this hl hk (le_of_not_ge hkl)).symm
  refine natCast_zsmul_eq_of_zmod_eq hk ?_
  rw [← TateModule.toZModPow_eq_appr, ← PadicInt.zmod_cast_comp_toZModPow k l hkl, RingHom.comp_apply,
    TateModule.toZModPow_eq_appr, ZMod.castHom_apply, ZMod.cast_natCast (pow_dvd_pow p hkl)]


public theorem coe_smul (a : ℤ_[p]) (x : PrimaryTorsion p M) {k : ℕ} (hk : p ^ k • (x : M) = 0) :
    ((a • x : PrimaryTorsion p M) : M) = ((a.appr k : ℕ) : ℤ) • (x : M) :=
  appr_zsmul_eq_appr_zsmul a (Classical.choose_spec x.2) hk


public theorem coe_natCast_smul (c : ℕ) (x : PrimaryTorsion p M) :
    (((c : ℤ_[p]) • x : PrimaryTorsion p M) : M) = c • (x : M) := by
  obtain ⟨k, hk⟩ := x.2
  rw [coe_smul _ x hk, ← natCast_zsmul]
  refine natCast_zsmul_eq_of_zmod_eq hk ?_
  rw [← TateModule.toZModPow_eq_appr, map_natCast]


public theorem natCast_smul_eq_nsmul (c : ℕ) (x : PrimaryTorsion p M) : ((c : ℤ_[p]) • x) = c • x :=
  Subtype.ext (by rw [coe_natCast_smul, AddSubgroup.coe_nsmul])


public theorem coe_intCast_smul (c : ℤ) (x : PrimaryTorsion p M) :
    (((c : ℤ_[p]) • x : PrimaryTorsion p M) : M) = c • (x : M) := by
  rw [Int.cast_smul_eq_zsmul, AddSubgroup.coe_zsmul]


public theorem pow_smul_eq_zero (x : PrimaryTorsion p M) {k : ℕ} (hk : p ^ k • (x : M) = 0) :
    ((p : ℤ_[p]) ^ k) • x = 0 := by
  rw [← Nat.cast_pow, natCast_smul_eq_nsmul]
  exact Subtype.ext (by rw [AddSubgroup.coe_nsmul, hk, AddSubgroup.coe_zero])


public theorem isTorsion' (x : PrimaryTorsion p M) : ∃ k : ℕ, ((p : ℤ_[p]) ^ k) • x = 0 := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, pow_smul_eq_zero x hk⟩


public theorem smul_eq_zero_of_mem_span {k : ℕ} {a : ℤ_[p]} (ha : a ∈ Ideal.span {(p : ℤ_[p]) ^ k})
    (x : PrimaryTorsion p M) (hk : p ^ k • (x : M) = 0) : a • x = 0 := by
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 ha
  rw [mul_smul, pow_smul_eq_zero x hk, smul_zero]


public theorem coe_smul_eq_smul [Module ℤ_[p] M] (a : ℤ_[p]) (x : PrimaryTorsion p M) :
    ((a • x : PrimaryTorsion p M) : M) = a • (x : M) := by
  obtain ⟨k, hk⟩ := x.2
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec k a)
  have ha : a = ((a.appr k : ℕ) : ℤ_[p]) + c * (p ^ k : ℕ) := by
    rw [Nat.cast_pow, hc, add_sub_cancel]
  have hkill : ((p ^ k : ℕ) : ℤ_[p]) • (x : M) = 0 := by
    rw [Nat.cast_smul_eq_nsmul]; exact hk
  conv_rhs => rw [ha]
  rw [add_smul, mul_smul, hkill, smul_zero, add_zero, Nat.cast_smul_eq_nsmul, coe_smul a x hk, natCast_zsmul]

end Module

section Map

variable {N : Type} [AddCommGroup N]


public theorem map_mem (f : M →+ N) (x : PrimaryTorsion p M) : f x ∈ PrimaryTorsion p N := by
  obtain ⟨k, hk⟩ := x.2
  exact ⟨k, by rw [← map_nsmul, hk, map_zero]⟩

variable [Fact p.Prime]


@[simp] public theorem coe_map (f : M →+ N) (x : PrimaryTorsion p M) : ((map f x : PrimaryTorsion p N) : N) = f x :=
  rfl


public theorem map_id : map (AddMonoidHom.id M) = (LinearMap.id : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p M) :=
  LinearMap.ext fun _ => rfl


public theorem map_comp {P : Type} [AddCommGroup P] (g : N →+ P) (f : M →+ N) :
    (map (g.comp f) : PrimaryTorsion p M →ₗ[ℤ_[p]] PrimaryTorsion p P) = (map g).comp (map f) :=
  LinearMap.ext fun _ => rfl

end Map

section Tate

variable (p M) [Fact p.Prime]


@[simp] public theorem coe_ofTateModule (n : ℕ) (x : TateModule p M) :
    ((ofTateModule p M n x : PrimaryTorsion p M) : M) = (x : ℕ → M) n := rfl


public theorem pow_smul_ofTateModule (n : ℕ) (x : TateModule p M) : ((p : ℤ_[p]) ^ n) • ofTateModule p M n x = 0 :=
  pow_smul_eq_zero _ (by rw [coe_ofTateModule, ← natCast_zsmul]; exact TateModule.torsion x n)


public theorem natCast_smul_ofTateModule_succ (n : ℕ) (x : TateModule p M) :
    (p : ℤ_[p]) • ofTateModule p M (n + 1) x = ofTateModule p M n x :=
  Subtype.ext (by
    rw [natCast_smul_eq_nsmul, AddSubgroup.coe_nsmul, coe_ofTateModule, coe_ofTateModule, ← natCast_zsmul]
    exact TateModule.compat x n)

end Tate

end PrimaryTorsion
