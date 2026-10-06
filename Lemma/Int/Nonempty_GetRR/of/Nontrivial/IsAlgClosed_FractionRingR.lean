import Mathlib
import sympy.Basic

open TensorProduct

/--
[AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_exists_algHom_of_finite_of_valuationRing_of_isAlgClosed.lean)
-/
@[main]
private lemma main
  [CommRing R] [IsDomain R] [ValuationRing R] [CommRing D] [Algebra R D] [Module.Finite R D]
-- given
  (hC : IsAlgClosed (FractionRing R))
  (hD : Nontrivial (TensorProduct R (FractionRing R) D)) :
-- imply
  Nonempty (D →ₐ[R] R) := by
-- proof
  classical
  haveI := hC
  haveI := hD
  set K := FractionRing R

  haveI : Module.Finite K (K ⊗[R] D) := inferInstance
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (K ⊗[R] D)
  letI : Field ((K ⊗[R] D) ⧸ 𝔪) := Ideal.Quotient.field 𝔪
  haveI : Module.Finite K ((K ⊗[R] D) ⧸ 𝔪) := inferInstance
  haveI : Algebra.IsAlgebraic K ((K ⊗[R] D) ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite K _
  haveI : Module.IsTorsionFree K ((K ⊗[R] D) ⧸ 𝔪) :=
    Module.IsTorsionFree.of_smul_eq_zero (fun r m h => by
      by_cases hr : r = 0
      · exact Or.inl hr
      · right; rw [← one_smul K m, ← inv_mul_cancel₀ hr, mul_smul, h, smul_zero])
  let χ : (K ⊗[R] D) →ₐ[K] K := (IsAlgClosed.lift (R := K) (S := (K ⊗[R] D) ⧸ 𝔪) (M := K)).comp (Ideal.Quotient.mkₐ K 𝔪)

  let θ : D →ₐ[R] K := (χ.restrictScalars R).comp Algebra.TensorProduct.includeRight

  haveI : Algebra.IsIntegral R D := Algebra.IsIntegral.of_finite R D
  haveI : IsIntegrallyClosed R := inferInstance
  have hθ : ∀ x : D, θ x ∈ (⊥ : Subalgebra R K) := by
    intro x
    have hint : IsIntegral R (θ x) := (Algebra.IsIntegral.isIntegral x).map θ
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := R) (K := K)).1 hint
    exact Algebra.mem_bot.2 ⟨y, hy⟩
  let θ' : D →ₐ[R] (⊥ : Subalgebra R K) := θ.codRestrict ⊥ hθ
  exact ⟨(Algebra.botEquivOfInjective (IsFractionRing.injective R K)).toAlgHom.comp θ'⟩


-- created on 2026-10-05
