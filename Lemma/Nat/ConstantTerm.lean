import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AutomorphicForm_ConstantTerm
open AutomorphicForm MeasureTheory


/--
[AutomorphicForm_constantTerm_rightTranslate](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AutomorphicForm_constantTerm_rightTranslate.lean)
-/
@[path]
private lemma main
  [MeasurableSpace Q] [Group G]
  {μ : Measure Q}
  {u : Q → G}
  {f : G → ℂ}
  {g h : G} :
-- imply
  constantTerm μ u (fun x => f (x * h)) g = constantTerm μ u f (g * h) := by
-- proof
  simp only [constantTerm, constantTermIntegrand, mul_assoc]


-- created on 2026-10-23
