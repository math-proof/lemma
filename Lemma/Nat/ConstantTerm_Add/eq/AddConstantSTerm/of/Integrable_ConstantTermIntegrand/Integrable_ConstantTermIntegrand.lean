import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AutomorphicForm_ConstantTerm
open AutomorphicForm MeasureTheory


/--
[AutomorphicForm_constantTerm_add](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_constantTerm_add.lean)
-/
@[path]
private lemma main
  [MeasurableSpace Q] [Group G]
  {μ : Measure Q}
  {u : Q → G}
  {f₁ f₂ : G → ℂ}
  {g : G}
-- given
  (hf : Integrable (constantTermIntegrand u f₁ g) μ)
  (hg : Integrable (constantTermIntegrand u f₂ g) μ) :
-- imply
  constantTerm μ u (fun x => f₁ x + f₂ x) g
      = constantTerm μ u f₁ g + constantTerm μ u f₂ g := by
-- proof
  simpa [constantTerm, constantTermIntegrand] using integral_add hf hg


-- created on 2026-10-23
