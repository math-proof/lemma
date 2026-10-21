import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[CommGroup_index_range_powMonoidHom_eq_pow_finrank](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CommGroup_index_range_powMonoidHom_eq_pow_finrank.lean)
-/
@[path]
private lemma main
  {F : Type u} [CommGroup F] [Group.FG F]
  (htf : ∀ (x : F) (m : ℕ), 0 < m → x ^ m = 1 → x = 1)
  {n : ℕ} (hn : 0 < n) :
  -- imply
  (powMonoidHom n : MonoidHom F F).range.index = n ^ Module.finrank ℤ (Additive F) := by
  -- proof
  classical
  let _ : NeZero n := ⟨hn.ne'⟩
  let _ : Module.Finite ℤ (Additive F) := Module.Finite.iff_addGroup_fg.mpr inferInstance
  let _ : NoZeroSMulDivisors ℤ (Additive F) := by
    refine ⟨fun {c x} h => ?_⟩
    by_contra hne
    obtain ⟨hc, hx⟩ := not_or.mp hne
    apply hx
    have h' : (c.natAbs : ℤ) • x = 0 := by
      obtain hc' | hc' := Int.natAbs_eq c
      ·
        rwa [← hc']
      ·
        rw [show (c.natAbs : ℤ) = -c by omega, neg_smul, h, neg_zero]
    rw [natCast_zsmul] at h'
    have hpow : Additive.toMul x ^ c.natAbs = 1 := by
      rw [← toMul_nsmul, h']
      rfl
    have h2 := htf (Additive.toMul x) c.natAbs (Int.natAbs_pos.mpr hc) hpow
    refine Additive.toMul.injective ?_
    rw [h2]
    rfl
  let _ : Module.Free ℤ (Additive F) := Module.free_of_finite_type_torsion_free'
  let b := Module.finBasis ℤ (Additive F)
  let e := b.equivFun
  let ψ : Additive F →+ (Fin (Module.finrank ℤ (Additive F)) → ZMod n) := ((Int.castAddHom (ZMod n)).compLeft (Fin (Module.finrank ℤ (Additive F)))).comp e.toLinearMap.toAddMonoidHom
  have hψ : ∀ x i, ψ x i = ((e x i : ℤ) : ZMod n) := fun x i => rfl
  have hsurj : Function.Surjective ψ := by
    intro t
    refine ⟨e.symm (fun i => ((t i).val : ℤ)), ?_⟩
    funext i
    rw [hψ, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hker : Subgroup.toAddSubgroup ((powMonoidHom n : MonoidHom F F).range) = ψ.ker := by
    ext x
    constructor
    ·
      rintro ⟨y, hy⟩
      rw [AddMonoidHom.mem_ker]
      have hx : x = n • Additive.ofMul y := by
        rw [← ofMul_pow, ← powMonoidHom_apply, hy]
        rfl
      funext i
      rw [hψ, hx, map_nsmul, Pi.smul_apply, nsmul_eq_mul, Int.cast_mul, Int.cast_natCast, ZMod.natCast_self, zero_mul, Pi.zero_apply]
    ·
      intro hx
      rw [AddMonoidHom.mem_ker] at hx
      have hdiv : ∀ i, (n : ℤ) ∣ e x i := fun i => by
        have hi := congrFun hx i
        rw [hψ, Pi.zero_apply] at hi
        apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp hi
      choose c hc using hdiv
      refine ⟨Additive.toMul (e.symm c), ?_⟩
      rw [powMonoidHom_apply, ← toMul_nsmul]
      congr 1
      apply e.injective
      rw [map_nsmul, LinearEquiv.apply_symm_apply]
      funext i
      rw [Pi.smul_apply, nsmul_eq_mul, hc i]
  rw [← Subgroup.index_toAddSubgroup, hker, ← AddMonoidHom.comap_bot, AddSubgroup.index_comap_of_surjective _ hsurj, AddSubgroup.index_bot, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]


-- created on 2026-10-20
