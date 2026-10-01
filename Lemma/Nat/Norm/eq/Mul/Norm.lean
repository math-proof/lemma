import sympy.functions.elementary.complexes
import sympy.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2


@[main]
private lemma main
  {n : ℕ}
  {x : EuclideanSpace ℂ (Fin n)}
  {a : ℂ} :
-- imply
  ‖a • x‖ = ‖a‖ * ‖x‖ :=
-- proof
  norm_smul a x


-- created on 2026-09-27
