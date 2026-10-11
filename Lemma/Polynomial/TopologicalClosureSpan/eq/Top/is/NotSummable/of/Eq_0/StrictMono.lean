import Mathlib
import sympy.Basic
import sympy.calculus.functional_analysis.MuntzSzasz

/--
[MuntzSzasz](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/FunctionalAnalysis/MuntzSzasz.lean)
-/
@[path]
private lemma muntz_szasz_nat_iff
-- given
  (Λ : ℕ → ℕ)
  (hΛ_strict : StrictMono Λ)
  (hΛ_zero : Λ 0 = 0) :
-- imply
  (Submodule.span ℝ (Set.range (fun n : ℕ =>
    ((Polynomial.X : Polynomial ℝ) ^ Λ n).toContinuousMapOn (Set.Icc (0 : ℝ) 1)))).topologicalClosure = ⊤
    ↔ ¬Summable (fun n : ℕ => ((Λ (n + 1) : ℝ)⁻¹)) := by
-- proof
  apply FunctionalAnalysis.MuntzSzaszWanted.muntz_szasz_nat Λ hΛ_strict hΛ_zero

-- created on 2026-10-10
