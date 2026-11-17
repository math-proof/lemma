import Mathlib
import Def.FLTPrelim_Ramification

set_option autoImplicit false

noncomputable section

namespace NumberField.LevelArith

variable (S : Finset Nat.Primes)

def IsSUnitMax (x : (AlgebraicClosure ℚ)ˣ) : Prop :=
  (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ),
      (FiniteDimensional ℚ F ∧
        ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ),
          A.LiesOverPrime (q : ℕ) → A.inertiaSubgroupIn ℚ ≤ F.fixingSubgroup) ∧
      (x : AlgebraicClosure ℚ) ∈ F) ∧
    ∀ q : Nat.Primes, q ∉ S → ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime (q : ℕ) →
      (x : AlgebraicClosure ℚ) ∈ A ∧ ((x⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ∈ A

def sUnitsMax : Subgroup (AlgebraicClosure ℚ)ˣ where
  carrier := {x | IsSUnitMax S x}
  one_mem' := by
    refine ⟨⟨⊥, ?unram, by simp⟩, fun q _ A _ => ⟨by simp, by simp⟩⟩
    refine ⟨inferInstance, fun q _ A _ σ _ => ?_⟩
    rw [IntermediateField.mem_fixingSubgroup_iff]
    rintro x hx
    obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.1 hx
    exact σ.commutes r
  mul_mem' := by
    rintro x y ⟨⟨F, ⟨hFdim, hF⟩, hxF⟩, hx⟩ ⟨⟨F', ⟨hF'dim, hF'⟩, hyF'⟩, hy⟩
    have := hFdim
    have := hF'dim
    refine ⟨⟨F ⊔ F', ⟨IntermediateField.finiteDimensional_sup F F', fun q hq A hA σ hσ => ?_⟩, ?_⟩,
      fun q hq A hA => ⟨?_, ?_⟩⟩
    · rw [IntermediateField.fixingSubgroup_sup]
      exact ⟨hF q hq A hA hσ, hF' q hq A hA hσ⟩
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
