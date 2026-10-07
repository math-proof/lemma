import Mathlib
import sympy.Basic

open Polynomial

/--
[Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_Finite_quotient_of_isUnit_leadingCoeff_of_mem.lean)
-/
@[main]
private lemma main
  {R : Type u} [CommRing R]
  {A : Type v} [CommRing A] [Algebra R A] [Algebra R[X] A] [IsScalarTower R R[X] A] [Module.Finite R[X] A]
  {N : R[X]}
  {I : Ideal A}
-- given
  (hN : IsUnit N.leadingCoeff)
  (hNI : algebraMap R[X] A N ∈ I) :
-- imply
  Module.Finite R (A ⧸ I) := by
-- proof
  obtain ⟨c, hc⟩ := hN
  set N' : R[X] := C (↑c⁻¹ : R) * N with hN'def
  have hN' : N'.Monic := by
    refine monic_C_mul_of_mul_leadingCoeff_eq_one ?_
    rw [← hc, Units.inv_mul]
  have hN'I : algebraMap R[X] A N' ∈ I := by
    rw [hN'def, map_mul]
    exact I.mul_mem_left _ hNI

  let P : Ideal R[X] := Ideal.span {N'}
  have : Module.Finite R (R[X] ⧸ P) := hN'.finite_quotient
  have : Module.Finite (R[X] ⧸ P) (TensorProduct R[X] (R[X] ⧸ P) A) := inferInstance
  have : Module.Finite R (TensorProduct R[X] (R[X] ⧸ P) A) := Module.Finite.trans (R[X] ⧸ P) _
  let J : Ideal A := P.map (algebraMap R[X] A)

  let e₁ : TensorProduct R[X] (R[X] ⧸ P) A ≃ₗ[R[X]] A ⧸ (P • (⊤ : Submodule R[X] A)) :=
    TensorProduct.quotTensorEquivQuotSMul A P
  let e₂ : (A ⧸ (P • (⊤ : Submodule R[X] A))) ≃ₗ[R[X]] A ⧸ (J.restrictScalars R[X]) :=
    Submodule.quotEquivOfEq _ _ (Ideal.smul_top_eq_map P)
  let e₃ : (A ⧸ (J.restrictScalars R[X])) ≃ₗ[R[X]] A ⧸ J := Submodule.Quotient.restrictScalarsEquiv R[X] J
  have hJ : Module.Finite R (A ⧸ J) :=
    Module.Finite.equiv ((e₁.trans (e₂.trans e₃)).restrictScalars R)

  have hJI : J ≤ I := by
    rw [Ideal.map_le_iff_le_comap, Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact hN'I
  exact Module.Finite.of_surjective (Ideal.Quotient.factorₐ R hJI).toLinearMap (Ideal.Quotient.factor_surjective hJI)


-- created on 2026-10-05
