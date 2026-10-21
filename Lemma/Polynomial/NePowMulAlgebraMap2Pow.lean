import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_DualAssembly_sq_ne_natCast_sq_mul_of_joint_eigenvector_of_pow_eq_one_of_aeval_eq_zero_noFree.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {T : Type} [AddCommGroup T] [Module ℤ_[p] T]
  {K : Type} [Field K] [IsAlgClosed K] [CharZero K] [Algebra ℤ_[p] K]
  {A D : Module.End ℤ_[p] T}
  {m c : ℕ}
  {P : Polynomial ℤ}
  {v : K ⊗[ℤ_[p]] T}
  {a e : K}
  -- given
  (hm : 0 < m)
  (hD : D ^ m = 1)
  (hPm : P.Monic)
  (hPA : Polynomial.aeval A P = 0)
  (hroots : ∀ z : ℂ, Polynomial.aeval z P = 0 → ‖z‖ < c)
  (hv : v ≠ 0)
  (hA : A.baseChange K v = a • v)
  (hDv : D.baseChange K v = e • v) :
  -- imply
  a ^ 2 ≠ (algebraMap ℤ_[p] K ((c : ℕ) : ℤ_[p])) ^ 2 * e := by
  -- proof
  classical
  intro hae
  have hbc : ∀ (Q : Polynomial ℤ_[p]) (f : Module.End ℤ_[p] T), (Polynomial.aeval f Q).baseChange K = Polynomial.aeval (f.baseChange K) Q := by
    intro Q f
    refine Polynomial.induction_on' Q ?_ ?_
    ·
      intro q r hq hr
      rw [map_add, map_add, LinearMap.baseChange_add, hq, hr]
    ·
      intro n z
      have hpow : ∀ k : ℕ, (f ^ k).baseChange K = f.baseChange K ^ k := by
        intro k
        induction k
        · rw [pow_zero, pow_zero, LinearMap.baseChange_one]
        ·
          rename_i k ih
          rw [pow_succ, pow_succ, LinearMap.baseChange_mul, ih]
      rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, smul_one_mul, smul_one_mul, LinearMap.baseChange_smul, hpow]
  have hroot : ∀ (Q : Polynomial ℤ) (f : Module.End ℤ_[p] T), Polynomial.aeval f Q = 0 → ∀ (u : K ⊗[ℤ_[p]] T) (x : K), u ≠ 0 → f.baseChange K u = x • u → Polynomial.aeval x Q = 0 := by
    intro Q f hfQ u x hu hx
    set Qp : Polynomial ℤ_[p] := Q.map (algebraMap ℤ ℤ_[p]) with hQp
    have hQK : Polynomial.aeval (f.baseChange K) Qp = 0 := by
      rw [← hbc, hQp, Polynomial.aeval_map_algebraMap, hfQ, LinearMap.baseChange_zero]
    have hev : Module.End.HasEigenvector (f.baseChange K) x u := ⟨Iff.mpr Module.End.mem_eigenspace_iff hx, hu⟩
    have h1 := Module.End.aeval_apply_of_hasEigenvector (p := Qp.map (algebraMap ℤ_[p] K)) hev
    rw [Polynomial.aeval_map_algebraMap, hQK, LinearMap.zero_apply, Polynomial.eval_map_algebraMap, hQp, Polynomial.aeval_map_algebraMap] at h1
    apply (Iff.mp smul_eq_zero h1.symm).resolve_right hu
  have hPa : Polynomial.aeval a P = 0 := hroot P A hPA v a hv hA
  have hDQ : Polynomial.aeval D (Polynomial.X ^ m - 1 : Polynomial ℤ) = 0 := by
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, hD, sub_self]
  have hem : e ^ m = 1 := by
    have := hroot _ D hDQ v e hv hDv
    rw [map_sub, map_pow, Polynomial.aeval_X, map_one, sub_eq_zero] at this
    apply this
  have hia : IsIntegral ℤ a := ⟨P, hPm, hPa⟩
  have hie : IsIntegral ℤ e := by
    refine ⟨Polynomial.X ^ m - 1, Polynomial.monic_X_pow_sub_C 1 hm.ne', ?_⟩
    rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_one, hem, sub_self]
  have hqa : IsIntegral ℚ a := hia.tower_top
  have hqe : IsIntegral ℚ e := hie.tower_top
  let S : Subalgebra ℚ K := Algebra.adjoin ℚ {a, e}
  have hadj : ∀ x ∈ ({a, e} : Set K), IsIntegral ℚ x := by
    intro x hx
    obtain rfl | hx := hx
    · apply hqa
    ·
      rw [Set.mem_singleton_iff] at hx
      rw [hx]
      apply hqe
  let _ : Algebra.IsIntegral ℚ S := Algebra.IsIntegral.adjoin hadj
  let _ : Algebra.IsAlgebraic ℚ S := Algebra.IsIntegral.isAlgebraic
  let ι : S →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have ha' : a ∈ S := Algebra.subset_adjoin (Set.mem_insert a {e})
  have he' : e ∈ S := Algebra.subset_adjoin (Set.mem_insert_of_mem a (Set.mem_singleton e))
  set PQ : Polynomial ℚ := P.map (algebraMap ℤ ℚ) with hPQ
  have hna : ‖ι ⟨a, ha'⟩‖ < c := by
    apply hroots
    have h1 : Polynomial.aeval (⟨a, ha'⟩ : S) PQ = 0 := by
      apply Subtype.ext
      rw [Polynomial.aeval_subalgebra_coe, hPQ, Polynomial.aeval_map_algebraMap]
      apply hPa
    have h2 := congrArg ι h1
    rw [← Polynomial.aeval_algHom_apply, map_zero, hPQ, Polynomial.aeval_map_algebraMap] at h2
    apply h2
  have hne : ‖ι ⟨e, he'⟩‖ = 1 := by
    have h1 : (⟨e, he'⟩ : S) ^ m = 1 := by
      apply Subtype.ext
      simp [hem]
    have h2 : (ι ⟨e, he'⟩) ^ m = 1 := by
      rw [← map_pow, h1, map_one]
    apply Iff.mp (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne') _
    rw [← norm_pow, h2, norm_one]
  have haeS : (⟨a, ha'⟩ : S) ^ 2 = ((c : ℚ) • 1 : S) ^ 2 * ⟨e, he'⟩ := by
    apply Subtype.ext
    simp only [Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_smul, Subalgebra.coe_one]
    rw [hae]
    simp
  have haeC : ι ⟨a, ha'⟩ ^ 2 = (c : ℂ) ^ 2 * ι ⟨e, he'⟩ := by
    rw [← map_pow, haeS, map_mul, map_pow, map_smul, map_one]
    simp
  have hlt : ‖ι ⟨a, ha'⟩ ^ 2‖ < (c : ℝ) ^ 2 := by
    rw [norm_pow]
    apply pow_lt_pow_left₀ hna (norm_nonneg _) two_ne_zero
  rw [haeC, norm_mul, norm_pow, Complex.norm_natCast, hne, mul_one] at hlt
  apply lt_irrefl _ hlt


-- created on 2026-10-20
