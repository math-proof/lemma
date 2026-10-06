import Mathlib
import sympy.Basic


/--
[IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IntermediateField_finiteDimensional_and_isGalois_adjoin_of_forall_algEquiv_apply_mem.lean)
-/
@[main]
private lemma main
  {K : Type u} [Field K]
  {Ω : Type v} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
  {S : Set Ω}
-- given
  (hS : S.Finite)
  (hsep : ∀ x ∈ S, IsSeparable K x)
  (hstab : ∀ σ : Ω ≃ₐ[K] Ω, ∀ x ∈ S, σ x ∈ S) :
-- imply
  FiniteDimensional K ↥(IntermediateField.adjoin K S) ∧ IsGalois K ↥(IntermediateField.adjoin K S) := by
-- proof
  haveI : Finite ↑S := hS.to_subtype
  haveI : Normal K Ω := IsAlgClosure.normal K Ω
  have hfd : FiniteDimensional K ↥(IntermediateField.adjoin K S) :=
    IntermediateField.finiteDimensional_adjoin fun x hx => (hsep x hx).isIntegral
  haveI : Algebra.IsSeparable K ↥(IntermediateField.adjoin K S) :=
    (IntermediateField.isSeparable_adjoin_iff_isSeparable K Ω).mpr hsep
  haveI : Normal K ↥(IntermediateField.adjoin K S) := by
    rw [IntermediateField.normal_iff_forall_map_le']
    intro σ
    rw [IntermediateField.adjoin_map]
    apply IntermediateField.adjoin.mono
    rintro _ ⟨x, hx, rfl⟩
    exact hstab σ x hx
  exact ⟨hfd, IsGalois.mk⟩


-- created on 2026-10-05
