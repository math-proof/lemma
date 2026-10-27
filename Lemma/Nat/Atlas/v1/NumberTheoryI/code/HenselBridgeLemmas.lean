import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.NumberTheoryI.code.HenselBridgeLemmas
open KroneckerWeber
open scoped Padic


namespace KroneckerWeber

/--
[isPrimitiveRoot_mem_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselBridgeLemmas.lean)
-/
@[path]
lemma isPrimitiveRoot_mem_integralClosure
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [Field L]
  [Algebra ℚ_[p] L]
  {ζ : L}
-- given
  (hζ : IsPrimitiveRoot ζ p) :
-- imply
  ζ ∈ integralClosure ℤ_[p] L :=
-- proof
  (hζ.isIntegral hp.out.pos).tower_top

end KroneckerWeber

namespace KroneckerWeber

/--
[natCast_p_mem_maximalIdeal_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselBridgeLemmas.lean)
-/
@[path]
lemma natCast_p_mem_maximalIdeal_integralClosure
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  let _ := CyclotomicDVR.isLocalRing p L (p : integralClosure ℤ_[p] L) ∈ IsLocalRing.maximalIdeal (integralClosure ℤ_[p] L) := by
-- proof
  intro _
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[p] L).injective
  rw [IsLocalRing.mem_maximalIdeal]
  intro hu
  have hpn : ¬ IsUnit (p : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_p]
    exact ne_of_lt (inv_lt_one_of_one_lt₀ (Nat.one_lt_cast.mpr hp.out.one_lt))
  apply hpn
  obtain ⟨u, hu_eq⟩ := hu
  have hp_ne_Qp : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
  have hinv_integral : IsIntegral ℤ_[p] ((p : L)⁻¹) := by
    have hval : (u : integralClosure ℤ_[p] L).val = (p : L) := congr_arg Subtype.val hu_eq
    have hval_inv : (↑(u⁻¹ : (integralClosure ℤ_[p] L)ˣ) : integralClosure ℤ_[p] L).val =
      (p : L)⁻¹ := by
      have h1 := Units.mul_inv u
      have h2 : (u : integralClosure ℤ_[p] L).val *
        (↑(u⁻¹ : (integralClosure ℤ_[p] L)ˣ) : integralClosure ℤ_[p] L).val =
        (1 : L) := by
        change ((u : integralClosure ℤ_[p] L) * ↑u⁻¹).val = (1 : integralClosure ℤ_[p] L).val
        rw [h1]
      rw [hval] at h2
      have hp_ne_L : (p : L) ≠ 0 := Nat.cast_ne_zero.mpr hp.out.ne_zero
      exact (mul_left_cancel₀ hp_ne_L (by rw [mul_inv_cancel₀ hp_ne_L]; exact h2.symm)).symm
    rw [← hval_inv]
    exact (↑(u⁻¹) : integralClosure ℤ_[p] L).property
  have hpinv_eq : algebraMap ℚ_[p] L ((p : ℚ_[p])⁻¹) = (p : L)⁻¹ := by
    rw [map_inv₀, map_natCast]
  have hinv_integral_Qp : IsIntegral ℤ_[p] ((p : ℚ_[p])⁻¹) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ_[p] L).injective).mp (hpinv_eq ▸ hinv_integral)
  obtain ⟨x, hx⟩ := (IsIntegrallyClosed.isIntegral_iff.mp hinv_integral_Qp :
    (p : ℚ_[p])⁻¹ ∈ (algebraMap ℤ_[p] ℚ_[p]).range)
  have h1 : (p : ℤ_[p]) * x = 1 := by
    apply IsFractionRing.injective ℤ_[p] ℚ_[p]
    simp only [map_mul, map_natCast, map_one, hx, mul_inv_cancel₀ hp_ne_Qp]
  exact IsUnit.of_mul_eq_one _ h1

end KroneckerWeber

namespace KroneckerWeber

/--
[residueChar_integralClosure_eq_p](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselBridgeLemmas.lean)
-/
@[path]
lemma residueChar_integralClosure_eq_p
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  let _ := CyclotomicDVR.isLocalRing p L ringChar (IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) = p := by
-- proof
  intro _
  have hp_mem := natCast_p_mem_maximalIdeal_integralClosure p L
  have hp_zero : (p : IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) = 0 := by
    rw [show (p : IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) =
      IsLocalRing.residue _ (p : integralClosure ℤ_[p] L) from
      (map_natCast (IsLocalRing.residue _) p).symm]
    exact (IsLocalRing.residue_eq_zero_iff _).mpr hp_mem
  rw [ringChar.eq_iff]
  exact (CharP.charP_iff_prime_eq_zero hp.out).mpr hp_zero

end KroneckerWeber

namespace KroneckerWeber

/--
[charP_residueField_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselBridgeLemmas.lean)
-/
@[path]
lemma charP_residueField_integralClosure
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  {L : Type*}
  [Field L]
  [Algebra ℚ_[p] L]
  [IsCyclotomicExtension {p} ℚ_[p] L] :
-- imply
  let _ := CyclotomicDVR.isLocalRing p L CharP (IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) p := by
-- proof
  intro _
  have hrc := residueChar_integralClosure_eq_p p L
  rwa [ringChar.eq_iff] at hrc

end KroneckerWeber

namespace KroneckerWeber

/--
[geom_sum_prod_mem_integralClosure](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/HenselBridgeLemmas.lean)
-/
@[path]
lemma geom_sum_prod_mem_integralClosure
  {p : ℕ}
  [hp : Fact (Nat.Prime p)]
  [Field L]
  [Algebra ℚ_[p] L]
  {ζ : L}
-- given
  (hζ : IsPrimitiveRoot ζ p) :
-- imply
  geom_sum_prod ζ p ∈ integralClosure ℤ_[p] L := by
-- proof
  simp only [geom_sum_prod]
  apply Subalgebra.prod_mem
  intro k _
  apply Subalgebra.sum_mem
  intro i _
  exact Subalgebra.pow_mem _ (isPrimitiveRoot_mem_integralClosure hζ) _
end KroneckerWeber



-- created on 2026-10-23
