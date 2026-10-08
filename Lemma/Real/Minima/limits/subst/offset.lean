import sympy.concrete.expr_with_limits
import sympy.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic


@[main]
private lemma main
  {m : ℕ}
  {f : ℕ → ℝ} :
-- imply
  Minima (Set.Icc 1 m) f = Minima Set.univ fun n : Fin m => f ((n : ℕ) + 1) := by
-- proof
  simp only [Minima]
  congr 1
  ext z
  simp only [Set.mem_image, Set.mem_univ, true_and, Set.mem_Icc]
  constructor
  ·
    rintro ⟨k, ⟨hk1, hkm⟩, rfl⟩
    refine ⟨⟨k - 1, by omega⟩, ?_⟩
    simp only []
    apply congr_arg f
    omega
  ·
    rintro ⟨n, rfl⟩
    exact ⟨(n : ℕ) + 1, by omega, rfl⟩


-- created on 2026-10-08
