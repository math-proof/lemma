import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GaloisRep_StrictOrdinary
import Lemma.Int.P2MUtil

open GaloisRepAdic

/--
[GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_forall_quotientScalar_sq_eq_one](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_GaloisRepAdic_isStrictOrdinaryAt_of_detIsCyclotomic_of_forall_quotientScalar_sq_eq_one.lean)
-/

private lemma  exists_lineScalar_quotientScalar_det_eq {A V : Type} [CommRing A] [AddCommGroup V]
    [Module A V] (b : Module.Basis (Fin 2) A V) (M : Module.End A V)
    (hL : ∀ v ∈ A ∙ b 0, M v ∈ A ∙ b 0) :
    ∃ x z : A, (∀ w ∈ A ∙ b 0, M w = x • w) ∧ (∀ v, M v - z • v ∈ A ∙ b 0) ∧
      LinearMap.det M = x * z := by
  obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.mp
    (hL (b 0) (Submodule.mem_span_singleton_self _))
  obtain ⟨z, hz⟩ : ∃ z : A, b.repr (M (b 1)) 1 = z := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y : A, b.repr (M (b 1)) 0 = y := ⟨_, rfl⟩
  have hM1 : M (b 1) = y • b 0 + z • b 1 := by
    have := (b.sum_repr (M (b 1))).symm
    rwa [Fin.sum_univ_two, hy, hz] at this
  refine ⟨x, z, ?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [map_smul, ← hx, smul_comm]
  · have key : (A ∙ b 0).mkQ ∘ₗ (M - z • LinearMap.id) = 0 := by
      apply b.ext
      refine Fin.forall_fin_two.mpr ⟨?_, ?_⟩
      · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
          Submodule.Quotient.mk_eq_zero]
        exact Submodule.sub_mem _ (hL _ (Submodule.mem_span_singleton_self _))
          (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
      · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
          LinearMap.id_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
          Submodule.Quotient.mk_eq_zero]
        rw [hM1, add_sub_cancel_right]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    intro v
    have := LinearMap.congr_fun key v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, Submodule.mkQ_apply, LinearMap.zero_apply,
      Submodule.Quotient.mk_eq_zero] at this
    exact this
  · rw [← LinearMap.det_toMatrix b, Matrix.det_fin_two]
    have h00 : LinearMap.toMatrix b b M 0 0 = x := by
      rw [LinearMap.toMatrix_apply, ← hx]; simp
    have h10 : LinearMap.toMatrix b b M 1 0 = 0 := by
      rw [LinearMap.toMatrix_apply, ← hx]; simp
    have h11 : LinearMap.toMatrix b b M 1 1 = z := by
      rw [LinearMap.toMatrix_apply, hz]
    rw [h00, h10, h11]; ring

private lemma  sub_mul_mem_span_singleton_of_mul_self_eq_one {A : Type} [CommRing A] (x z a q : A)
    (hz : z * z = 1) (h : x * z - a ∈ Ideal.span {q}) : x - a * z ∈ Ideal.span {q} := by
  have hxz : x - a * z = z * (x * z - a) := by
    calc x - a * z = x * (z * z) - a * z := by rw [hz, mul_one]
      _ = z * (x * z - a) := by ring
  rw [hxz]
  exact Ideal.mul_mem_left _ _ h
@[path]
private lemma main
  [CommRing A] [IsLocalRing A]
  {ρ : GaloisRepAdic A}
  {p : ℕ}
-- given
  (hdet : ρ.DetIsCyclotomic p)
  (h : ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p → ∃ L : Submodule A ρ.V, (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧ (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧ (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L) ∧ (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ z : A, (∀ v : ρ.V, ρ.ρ σ v - z • v ∈ L) → z * z = 1)) :
-- imply
  ρ.IsStrictOrdinaryAt p := by
-- proof
  refine ⟨hdet.1, fun P hP => ?_⟩
  obtain ⟨L, ⟨b, hLb⟩, hD, hI, hsq⟩ := h P hP
  refine ⟨L, ⟨b, hLb⟩, hD, hI, fun σ hσ => ?_⟩
  subst hLb
  obtain ⟨x, z, hxL, hzq, hdetxz⟩ :=
    exists_lineScalar_quotientScalar_det_eq b (ρ.ρ σ) (hD σ hσ)
  refine ⟨x, z, hxL, hzq, fun n a hμ => ?_⟩
  have hc := hdet.2 n σ a hμ
  rw [hdetxz] at hc
  exact sub_mul_mem_span_singleton_of_mul_self_eq_one x z (a : A) _
    (hsq σ hσ z hzq) hc


-- created on 2026-10-23
