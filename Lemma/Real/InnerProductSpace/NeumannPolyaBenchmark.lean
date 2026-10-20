import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.InnerProductSpace.NeumannPolyaBenchmark
open TopologicalSpace
open EuclideanLaplacian


/--
[neumannPolyaEigenvalueBenchmark_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean)
-/
@[path]
private lemma neumannPolyaEigenvalueBenchmark_nonneg_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  0 ≤ neumannPolyaEigenvalueBenchmark Ω j := by
-- proof
  apply EuclideanLaplacian.neumannPolyaEigenvalueBenchmark_nonneg Ω j

/--
[neumannPolyaEigenvalueBenchmark_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/InnerProductSpace/NeumannPolyaBenchmark.lean)
-/
@[path]
private lemma neumannPolyaEigenvalueBenchmark_succ_eq
  {n : ℕ}
  {Ω : Opens (EuclideanSpace ℝ (Fin n))}
  {j : ℕ} :
-- imply
  neumannPolyaEigenvalueBenchmark Ω (j + 1) =
    polyaEigenvalueBenchmark Ω j := by
-- proof
  apply EuclideanLaplacian.neumannPolyaEigenvalueBenchmark_succ Ω j


-- created on 2026-10-20
