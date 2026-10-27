import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalRing_exists_monic_coeff_mem_maximalIdeal_aeval_mem_span_of_pow_mem.lean)
-/
@[path]
private lemma main
  [CommRing A] [IsLocalRing A] [CommRing S] [Algebra A S]
  (h T : S) [Module.Finite A (S ⧸ Ideal.span ({h} : Set S))]
  -- given
  (hnil : ∃ k : ℕ, (Ideal.Quotient.mk (Ideal.span ({h} : Set S)) T) ^ k ∈ (maximalIdeal A).map (algebraMap A (S ⧸ Ideal.span ({h} : Set S)))) :
  -- imply
  ∃ P : Polynomial A, P.Monic ∧ (∀ i : ℕ, i < P.natDegree → P.coeff i ∈ maximalIdeal A) ∧ Polynomial.aeval T P ∈ Ideal.span ({h} : Set S) := by
  -- proof
  classical
  set I : Ideal S := Ideal.span ({h} : Set S) with hI
  set M := S ⧸ I
  obtain ⟨k, hk⟩ := hnil
  set t : M := Ideal.Quotient.mk I T with ht
  have hk1 : t ^ (k + 1) ∈ (maximalIdeal A).map (algebraMap A M) := by
    rw [pow_succ']
    apply Ideal.mul_mem_left _ _ hk
  let φ : Module.End A M := Algebra.lmul A M (t ^ (k + 1))
  have hφ : LinearMap.range φ ≤ (maximalIdeal A) • (⊤ : Submodule A M) := by
    rintro m ⟨m', rfl⟩
    rw [Ideal.smul_top_eq_map]
    show t ^ (k + 1) * m' ∈ (maximalIdeal A).map (algebraMap A M)
    apply Ideal.mul_mem_right _ _ hk1
  obtain ⟨p, hpm, -, hpc, hpφ⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero A φ (maximalIdeal A) hφ
  have hpt : Polynomial.aeval (t ^ (k + 1)) p = 0 := by
    have h1 : Polynomial.aeval φ p = Algebra.lmul A M (Polynomial.aeval (t ^ (k + 1)) p) := by
      rw [Polynomial.aeval_algHom_apply]
    have h2 := congrArg (fun ψ : Module.End A M => ψ 1) (h1.symm.trans hpφ)
    simpa [Algebra.coe_lmul_eq_mul, LinearMap.mul_apply'] using h2
  refine ⟨Polynomial.expand A (k + 1) p, hpm.expand (Nat.succ_pos k), fun i hi => ?_, ?_⟩
  ·
    rw [Polynomial.coeff_expand (Nat.succ_pos k)]
    split_ifs with hdvd
    ·
      have hlt : i / (k + 1) < p.natDegree := by
        rw [Polynomial.natDegree_expand] at hi
        apply Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hi)
      have := hpc (i / (k + 1))
      apply Ideal.pow_le_self (Nat.sub_ne_zero_of_lt hlt) this
    · apply Submodule.zero_mem _
  ·
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk A, ← Polynomial.aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk, Polynomial.expand_aeval]
    apply hpt


-- created on 2026-10-20
