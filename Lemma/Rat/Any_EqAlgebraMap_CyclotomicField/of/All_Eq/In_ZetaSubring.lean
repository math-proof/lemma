import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_ModularCurve_LevelFunctionField
import Lemma.Int.P2MUtil

open ModularCurve

/--
[ModularCurve_exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ModularCurve_exists_algebraMap_int_eq_of_mem_zetaSubring_of_forall_algEquiv_apply_eq.lean)
-/
@[path]
private lemma main
  {q : ℕ} [Fact q.Prime]
  {c : CyclotomicField q ℚ}
-- given
  (hc : c ∈ zetaSubring q)
  (hfix : ∀ σ : CyclotomicField q ℚ ≃ₐ[ℚ] CyclotomicField q ℚ, σ c = c) :
-- imply
  ∃ m : ℤ, algebraMap ℤ (CyclotomicField q ℚ) m = c := by
  haveI hcyc : IsCyclotomicExtension {q} ℚ (CyclotomicField q ℚ) := CyclotomicField.isCyclotomicExtension q ℚ
  haveI : FiniteDimensional ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.finiteDimensional {q} ℚ (CyclotomicField q ℚ)
  haveI : IsGalois ℚ (CyclotomicField q ℚ) := IsCyclotomicExtension.isGalois {q} ℚ (CyclotomicField q ℚ)
  have hcbot : c ∈ (⊥ : IntermediateField ℚ (CyclotomicField q ℚ)) := by
-- proof
    rw [← IsGalois.fixedField_top]
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact hfix σ
  obtain ⟨r, hr⟩ := IntermediateField.mem_bot.mp hcbot
  have hζ : IsIntegral ℤ (zetaQ q) := (isPrimitiveRoot_zetaQ q).isIntegral (Fact.out : q.Prime).pos
  have hcint : IsIntegral ℤ c := adjoin_le_integralClosure hζ hc
  have hrint : IsIntegral ℤ r := by
    rw [← hr] at hcint
    exact (isIntegral_algHom_iff (algebraMap ℚ (CyclotomicField q ℚ)).toIntAlgHom
      (algebraMap ℚ (CyclotomicField q ℚ)).injective).mp hcint
  obtain ⟨m, hm⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp hrint
  refine ⟨m, ?_⟩
  rw [← hr, ← hm]
  simp


-- created on 2026-10-23
