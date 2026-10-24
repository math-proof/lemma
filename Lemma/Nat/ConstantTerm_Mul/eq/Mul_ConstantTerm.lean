import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AutomorphicForm_ConstantTerm
open AutomorphicForm MeasureTheory


/-- ported from external source -/
@[path]
private lemma main
  [MeasurableSpace Q] [Group G]
  {μ : Measure Q}
  {u : Q → G}
  {c : ℂ}
  {f : G → ℂ}
  {g : G} :
-- imply
  constantTerm μ u (fun x => c * f x) g = c * constantTerm μ u f g := by
-- proof
  simpa [constantTerm, constantTermIntegrand, smul_eq_mul] using
    integral_smul (μ := μ) c (fun q => f (u q * g))


-- created on 2026-10-23
