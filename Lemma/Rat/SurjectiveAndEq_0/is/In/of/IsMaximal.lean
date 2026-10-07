import Mathlib
import sympy.Basic


/--
[exists_residueField_of_isMaximal_of_finiteDimensional](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_exists_residueField_of_isMaximal_of_finiteDimensional.lean)
-/
@[main]
private lemma main
  {F : Type u} [Field F] [CharZero F]
  {A : Type v} [CommRing A] [Algebra F A] [FiniteDimensional F A]
  {𝔪 : Ideal A}
-- given
  (h𝔪 : 𝔪.IsMaximal) :
-- imply
  ∃ (K : Type v) (_ : Field K) (_ : Algebra F K) (_ : FiniteDimensional F K) (_ : Algebra.IsSeparable F K)
      (θ : A →ₐ[F] K), Function.Surjective θ ∧ ∀ a : A, θ a = 0 ↔ a ∈ 𝔪 := by
-- proof
  have := h𝔪
  let : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  have : FiniteDimensional F (A ⧸ 𝔪) := inferInstance
  have : Algebra.IsSeparable F (A ⧸ 𝔪) := Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨A ⧸ 𝔪, inferInstance, inferInstance, inferInstance, inferInstance, Ideal.Quotient.mkₐ F 𝔪,
    Ideal.Quotient.mkₐ_surjective F 𝔪, fun a => Ideal.Quotient.eq_zero_iff_mem⟩


-- created on 2026-10-05
