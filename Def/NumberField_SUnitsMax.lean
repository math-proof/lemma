import Mathlib
import Lemma.GroupCohomology.ContinuousUnramified

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

variable (S : Finset Nat.Primes)

def IsSUnitMax (x : (AlgebraicClosure ℚ)ˣ) : Prop :=
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), F.IsUnramifiedOutside S ∧ (x : AlgebraicClosure ℚ) ∈ F) ∧
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      (x : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A

def sUnitsMax : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | IsSUnitMax S x}
  one_mem' := ⟨⟨⊥, IntermediateField.isUnramifiedOutside_bot S, by simp⟩, fun q _ A _ => ⟨by simp, by simp⟩⟩
  mul_mem' := by
    rintro x y ⟨⟨F, hF, hxF⟩, hx⟩ ⟨⟨F', hF', hyF'⟩, hy⟩
    refine ⟨⟨F ⊔ F', hF.sup hF', ?_⟩, fun q hq A hA => ⟨?_, ?_⟩⟩
    · rw [Units.val_mul]; exact mul_mem ((le_sup_left : F ≤ F ⊔ F') hxF) ((le_sup_right : F' ≤ F ⊔ F') hyF')
    · rw [Units.val_mul]; exact A.toSubring.mul_mem (hx q hq A hA).1 (hy q hq A hA).1
    · rw [mul_inv_rev, Units.val_mul]; exact A.toSubring.mul_mem (hy q hq A hA).2 (hx q hq A hA).2
  inv_mem' := by
    rintro x ⟨⟨F, hF, hxF⟩, hx⟩
    refine ⟨⟨F, hF, ?_⟩, fun q hq A hA => ⟨(hx q hq A hA).2, by simpa using (hx q hq A hA).1⟩⟩
    rw [Units.val_inv_eq_inv_val]; exact inv_mem hxF


variable (L : IntermediateField ℚ (AlgebraicClosure ℚ))

def sUnitsMaxStable : Subgroup (AlgebraicClosure ℚ)ˣ :=
  ⨅ γ : ↥L.fixingSubgroup, (sUnitsMax S).comap (MulDistribMulAction.toMonoidHom (AlgebraicClosure ℚ)ˣ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)))


def sUnitsMaxSubmodule : Submodule ℤ (Additive (AlgebraicClosure ℚ)ˣ) := (Subgroup.toAddSubgroup (sUnitsMaxStable S L)).toIntSubmodule

end NumberField.LevelArith

end
