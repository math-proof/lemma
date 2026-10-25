/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/NumberTheory/Cyclotomic/IntermediateField.lean -/


import Def.NumberTheory.Cyclotomic.IntermediateField
import Lemma.Nat.Cyclotomic.IntermediateField
open scoped IntermediateField


example :
    ∃! K : IntermediateField ℚ (CyclotomicField 2 ℚ), Module.finrank ℚ K = 1 :=
  CyclotomicField.existsUnique_intermediateField_finrank 2 1 Nat.prime_two (by decide)

example :
    Module.finrank ℚ
      (CyclotomicField.intermediateFieldOfFinrank 5 2 Nat.prime_five (by decide)) = 2 := by
  simp

example (K : IntermediateField ℚ (CyclotomicField 5 ℚ)) :
    K = CyclotomicField.intermediateFieldOfFinrank 5 2 Nat.prime_five (by decide) ↔
      Module.finrank ℚ K = 2 :=
  CyclotomicField.eq_intermediateFieldOfFinrank_iff 5 2 Nat.prime_five (by decide) K

-- Generic API example: cyclotomic factors with the stated lcm generate the ambient field.
example (n₀ n₁ m : ℕ) [NeZero n₀] [NeZero n₁]
    (E₀ E₁ : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
    (hlcm : Nat.lcm n₀ n₁ = m) : E₀ ⊔ E₁ = ⊤ :=
  CyclotomicField.sup_eq_top_of_lcm_eq n₀ n₁ m E₀ E₁ hlcm

-- Generic API example: a strict extension of the first factor meets the second nontrivially.
example (n₀ n₁ m : ℕ) [NeZero n₀] [NeZero n₁]
    (E₀ E₁ F : IntermediateField ℚ (CyclotomicField m ℚ))
    [IsCyclotomicExtension {n₀} ℚ E₀] [IsCyclotomicExtension {n₁} ℚ E₁]
    (hlcm : Nat.lcm n₀ n₁ = m) (hE₀F : E₀ < F) : F ⊓ E₁ ≠ ⊥ :=
  CyclotomicField.inf_ne_bot_of_lt_of_lcm_eq n₀ n₁ m E₀ E₁ F hlcm hE₀F

-- Concrete coprime conductors: factors of conductors 2 and 3 generate the 6th field.
example (E₀ E₁ : IntermediateField ℚ (CyclotomicField 6 ℚ))
    [IsCyclotomicExtension {2} ℚ E₀] [IsCyclotomicExtension {3} ℚ E₁] :
    E₀ ⊔ E₁ = ⊤ := by
  let _ : NeZero 2 := ⟨by norm_num⟩
  let _ : NeZero 3 := ⟨by norm_num⟩
  exact CyclotomicField.sup_eq_top_of_lcm_eq 2 3 6 E₀ E₁ (by decide)

-- Concrete coprime conductors: a strict extension of the conductor-2 factor meets the
-- conductor-3 factor nontrivially inside the 6th cyclotomic field.
example (E₀ E₁ F : IntermediateField ℚ (CyclotomicField 6 ℚ))
    [IsCyclotomicExtension {2} ℚ E₀] [IsCyclotomicExtension {3} ℚ E₁]
    (hE₀F : E₀ < F) : F ⊓ E₁ ≠ ⊥ := by
  let _ : NeZero 2 := ⟨by norm_num⟩
  let _ : NeZero 3 := ⟨by norm_num⟩
  exact CyclotomicField.inf_ne_bot_of_lt_of_lcm_eq 2 3 6 E₀ E₁ F (by decide) hE₀F

