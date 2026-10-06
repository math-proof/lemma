import Mathlib
import sympy.Basic

open Filter Topology

/--
[Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Polynomial_aeval_eq_zero_of_forall_pos_aeval_sum_pow_smul_eq_zero.lean)
-/
@[main]
private lemma main
  {R D : ℕ}
  {N : Fin (D + 1) → Matrix (Fin R) (Fin R) ℂ}
  {q : Polynomial ℂ}
-- given
  (h : ∀ y : ℝ, 0 < y → Polynomial.aeval (∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a) q = 0) :
-- imply
  Polynomial.aeval (N 0) q = 0 := by
-- proof
  let S : ℝ → Matrix (Fin R) (Fin R) ℂ := fun y => ∑ a : Fin (D + 1), ((y : ℂ) ^ (a : ℕ)) • N a
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro a _
    exact ((Complex.continuous_ofReal.pow _).smul continuous_const)
  let f : ℝ → Matrix (Fin R) (Fin R) ℂ := fun y => Polynomial.aeval (S y) q
  have hf : Continuous f := (Polynomial.continuous_aeval q).comp hS
  have hS0 : S 0 = N 0 := by
    show ∑ a : Fin (D + 1), (((0 : ℝ) : ℂ) ^ (a : ℕ)) • N a = N 0
    rw [Fin.sum_univ_succ]
    simp
  have h1 : Tendsto f (𝓝[>] 0) (𝓝 (f 0)) := hf.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[>] 0) (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    exact (h y hy).symm
  have h3 : f 0 = 0 := tendsto_nhds_unique h1 h2
  have : f 0 = Polynomial.aeval (N 0) q := by show Polynomial.aeval (S 0) q = _; rw [hS0]
  rw [← this, h3]


-- created on 2026-10-05
