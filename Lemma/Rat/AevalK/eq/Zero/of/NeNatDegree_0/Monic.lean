import Mathlib
import sympy.Basic


/--
[ValuationSubring_exists_root_mem_of_monic](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_root_mem_of_monic.lean)
-/
@[path]
private lemma main
  [Field K] [IsAlgClosed K]
  {A : ValuationSubring K}
  {f : Polynomial A}
-- given
  (hf : f.Monic)
  (hd : f.natDegree ≠ 0) :
-- imply
  ∃ x : A, Polynomial.aeval (x : K) f = 0 := by
-- proof
  have hdeg : (f.map (algebraMap A K)).degree ≠ 0 := by
    rw [hf.degree_map]
    intro h
    exact hd (Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr h.le)
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (f.map (algebraMap A K)) hdeg
  have hint : IsIntegral A x := by
    refine ⟨f, hf, ?_⟩
    rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  have hyx : (y : K) = x := hy
  rw [Polynomial.aeval_def, hyx]
  rwa [Polynomial.IsRoot, Polynomial.eval_map] at hx


-- created on 2026-10-05
