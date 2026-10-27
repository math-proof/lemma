import Notation.Analysis.Complex.Complexes
import Initialize.Tactic.Attr.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2


@[path]
private lemma main
  {n : ℕ}
  {x : EuclideanSpace ℂ (Fin n)}
  {a : ℂ} :
-- imply
  ‖a • x‖ = ‖a‖ * ‖x‖ :=
-- proof
  norm_smul a x


-- created on 2023-06-24
