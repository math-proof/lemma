import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.DifferentialAnalysis.code.SchwartzCompleteness
open TemperedDistributions
open scoped SchwartzMap


/--
[schwartz_seminorm_cauchy_converges_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCompleteness.lean)
-/
@[path]
lemma schwartz_seminorm_cauchy_converges_aux
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
-- given
  (hcauchy : ∀ K : ℕ, ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - u m) < ε) :
-- imply
  ∃ v : 𝓢(E, F), ∀ K : ℕ, Filter.Tendsto (fun n => (Finset.Iic (K, K)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) (u n - v)) Filter.atTop (nhds 0) :=
-- proof
  TemperedDistributions.schwartz_seminorm_cauchy_converges u hcauchy

namespace TemperedDistributions

/--
[seminorm_cauchy_of_schwartzDist_cauchy](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCompleteness.lean)
-/
@[path]
lemma seminorm_cauchy_of_schwartzDist_cauchy
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F]
  {u : ℕ → 𝓢(E, F)}
  {k : ℕ}
-- given
  (hcauchy : ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → schwartzDist (u n) (u m) < ε) :
-- imply
  ∀ ε > 0, ∃ N, ∀ n m, N ≤ n → N ≤ m → supSeminorm k (u n - u m) < ε :=
-- proof
  schwartzDist_cauchy_implies_seminorm_cauchy u hcauchy k

end TemperedDistributions

/--
[instCompleteSpace_axiom](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SchwartzCompleteness.lean)
-/
@[path]
private lemma instCompleteSpace_axiom_eq
  [NormedAddCommGroup E]
  [NormedSpace ℝ E]
  [NormedAddCommGroup F]
  [NormedSpace ℝ F]
  [CompleteSpace F] :
-- imply
  CompleteSpace 𝓢(E, F) := by
-- proof
  apply instCompleteSpace_axiom


-- created on 2026-10-23
