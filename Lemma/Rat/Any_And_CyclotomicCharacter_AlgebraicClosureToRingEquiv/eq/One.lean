import Mathlib
import sympy.Basic
set_option synthInstance.maxHeartbeats 1600000
open IntermediateField


/--
[AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicClosure_exists_intermediateField_toZModPow_cyclotomicCharacter_eq_one.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {n : ℕ} :
-- imply
  ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
    ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ F, τ x = x) →
      PadicInt.toZModPow n
        ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
-- proof
  classical
  have hp0 : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hEn : ∀ i : ℕ, HasEnoughRootsOfUnity (AlgebraicClosure ℚ) (p ^ i) := fun i => inferInstance
  cases n with
  | zero =>
    exact ⟨⊥, inferInstance, fun τ _ => (ZMod.subsingleton_iff.2 (pow_zero p)).elim _ _⟩
  | succ n =>
    have hn : 0 < n.succ := Nat.succ_pos n
    have : NeZero (p ^ (n + 1)) := ⟨pow_ne_zero (n + 1) (Fact.out : p.Prime).ne_zero⟩
    obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure ℚ) (p ^ (n + 1))
    have hfix : ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
        (∀ x ∈ (ℚ⟮ζ⟯ : IntermediateField ℚ (AlgebraicClosure ℚ)), τ x = x) →
        PadicInt.toZModPow (n + 1)
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) = 1 := by
      intro σ hσ
      rw [cyclotomicCharacter.toZModPow, eq_comm]
      apply modularCyclotomicCharacter.unique
      intro t ht
      obtain ⟨i, -, rfl⟩ := (hζ.isUnit_unit NeZero.out).eq_pow_of_mem_rootsOfUnity ht
      rw [ZMod.val_one'', pow_one]
      · exact hσ (ζ ^ i) (pow_mem (IntermediateField.mem_adjoin_simple_self ℚ ζ) _)
      · exact (one_lt_pow₀ (Fact.out : p.Prime).one_lt hn.ne').ne'
    refine ⟨ℚ⟮ζ⟯, IntermediateField.adjoin.finiteDimensional (hζ.isIntegral (NeZero.pos _)).tower_top, hfix⟩


-- created on 2026-10-13
