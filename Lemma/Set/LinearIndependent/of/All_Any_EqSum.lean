import Mathlib
import sympy.Basic


/--
[LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearIndependent_of_forall_mem_span_exists_sum_zsmul_eq.lean)
-/
@[main]
private lemma main
  [AddCommGroup V] [Module ℝ V]
  {k : ℕ}
  {b₀ : Module.Basis (Fin k) ℝ V}
  {v : Fin k → V}
-- given
  (hgen : ∀ x ∈ Submodule.span ℤ (Set.range b₀), ∃ n : Fin k → ℤ, (∑ i, n i • v i) = x) :
-- imply
  LinearIndependent ℝ v := by
-- proof
  classical
  have : FiniteDimensional ℝ V := Module.Finite.of_basis b₀

  have hspan : ⊤ ≤ Submodule.span ℝ (Set.range v) := by
    rw [← b₀.span_eq]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨j, rfl⟩
    obtain ⟨n, hn⟩ := hgen (b₀ j) (Submodule.subset_span ⟨j, rfl⟩)
    rw [← hn]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [← Int.cast_smul_eq_zsmul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hcard : Fintype.card (Fin k) = Module.finrank ℝ V := by
    rw [Module.finrank_eq_card_basis b₀]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard


-- created on 2026-10-05
