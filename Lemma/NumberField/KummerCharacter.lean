import Mathlib

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

section KummerChar

variable (p : ℕ) [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (F : IntermediateField ℚ (AlgebraicClosure ℚ))

def kummerRoot (x : (↥F)ˣ) : AlgebraicClosure ℚ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

theorem kummerRoot_pow (x : (↥F)ˣ) : kummerRoot p F x ^ p = ((x : ↥F) : AlgebraicClosure ℚ) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((x : ↥F) : AlgebraicClosure ℚ) (Fact.out : p.Prime).pos)

theorem kummerRoot_ne_zero (x : (↥F)ˣ) : kummerRoot p F x ≠ 0 := fun h => by
  have := kummerRoot_pow p F x
  rw [h, zero_pow (Fact.out : p.Prime).ne_zero] at this
  exact (Units.ne_zero x) (Subtype.ext (by exact_mod_cast this.symm))

theorem div_kummerRoot_pow_eq_one (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ((σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x) ^ p = 1 := by
  rw [div_pow, ← map_pow, kummerRoot_pow, div_eq_one_iff_eq]
  · exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 σ.2 _ (x : ↥F).2
  · exact_mod_cast (Units.ne_zero x : (x : ↥F) ≠ 0)

include hζ in
theorem exists_kummerExp (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    ∃ i < p, ζ ^ i = (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) / kummerRoot p F x :=
  hζ.eq_pow_of_pow_eq_one (div_kummerRoot_pow_eq_one p F x σ)

def kummerChar (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) : ZMod p :=
  (Classical.choose (exists_kummerExp p ζ hζ F x σ) : ℕ)

theorem kummerChar_spec (x : (↥F)ˣ) (σ : ↥F.fixingSubgroup) :
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (kummerRoot p F x) = ζ ^ (kummerChar p ζ hζ F x σ).val * kummerRoot p F x := by
  obtain ⟨hi, h⟩ := Classical.choose_spec (exists_kummerExp p ζ hζ F x σ)
  rw [kummerChar, ZMod.val_natCast_of_lt hi, h, div_mul_cancel₀ _ (kummerRoot_ne_zero p F x)]

end KummerChar

end NumberField.LevelArith

end
