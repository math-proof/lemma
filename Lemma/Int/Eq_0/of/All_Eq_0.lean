import Mathlib
import sympy.Basic
open scoped TensorProduct


/--
[Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_eq_zero_of_forall_algHom_apply_eq_zero_of_isReduced_tensorProduct.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K]
  {B : Type u} [CommRing B] [Algebra R B] [NoZeroSMulDivisors R B] [IsReduced (TensorProduct R K B)] [Module.Finite K (TensorProduct R K B)]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [Algebra R Ω] [Algebra K Ω] [IsScalarTower R K Ω]
  {b : B}
-- given
  (hb : ∀ φ : B →ₐ[R] Ω, φ b = 0) :
-- imply
  b = 0 := by
-- proof
  classical
  set A := K ⊗[R] B with hA
  apply show ∀ b : B, (1 : K) ⊗ₜ[R] b = 0 → b = 0 by
    intro b hb0
    let _ : IsLocalizedModule (nonZeroDivisors R) (TensorProduct.mk R K B 1) := inferInstance
    obtain ⟨⟨s, hs⟩, hsb⟩ :=
      (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) (TensorProduct.mk R K B 1)).mp hb0
    apply (smul_eq_zero.mp hsb).resolve_left (nonZeroDivisors.ne_zero hs)
  set a : A := (1 : K) ⊗ₜ[R] b with ha
  have hpts : ∀ ψ : A →ₐ[K] Ω, ψ a = 0 := by
    intro ψ
    let φ : B →ₐ[R] Ω := (ψ.restrictScalars R).comp
      ((Algebra.TensorProduct.includeRight : B →ₐ[R] A))
    have := hb φ
    simp [φ] at this
    apply this
  by_contra hne
  let _ : IsArtinianRing A := IsArtinianRing.of_finite K A
  have hjac : (⊥ : Ideal A).jacobson = ⊥ := by
    rw [IsArtinianRing.jacobson_eq_radical]
    apply nilradical_eq_zero A
  have : a ∉ (⊥ : Ideal A).jacobson := by
    rw [hjac]
    simpa using hne
  rw [Ideal.jacobson, Submodule.mem_sInf] at this
  push Not at this
  obtain ⟨𝔪, ⟨-, h𝔪⟩, ha𝔪⟩ := this
  let _ : Ideal.IsMaximal 𝔪 := h𝔪
  let _ : IsDomain (A ⧸ 𝔪) := Ideal.Quotient.isDomain 𝔪
  let _ : Algebra.IsAlgebraic K (A ⧸ 𝔪) := Algebra.IsAlgebraic.of_finite K (A ⧸ 𝔪)
  let j : (A ⧸ 𝔪) →ₐ[K] Ω := IsAlgClosed.lift (R := K) (S := A ⧸ 𝔪) (M := Ω)
  have h0 : j (Ideal.Quotient.mk 𝔪 a) = 0 := by
    have := hpts (j.comp (Ideal.Quotient.mkₐ K 𝔪))
    simpa using this
  have h1 : Ideal.Quotient.mk 𝔪 a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  have hfield := (Ideal.Quotient.maximal_ideal_iff_isField_quotient 𝔪).mp h𝔪
  obtain ⟨c, hc⟩ := hfield.mul_inv_cancel h1
  have : j (Ideal.Quotient.mk 𝔪 a) * j c = 1 := by
    rw [← map_mul, hc, map_one]
  rw [h0, zero_mul] at this
  apply absurd this zero_ne_one


-- created on 2026-10-13
