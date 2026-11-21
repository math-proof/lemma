import Initialize.Tactic.Attr.Basic
import Instance.Analysis.SpecialFunctions.Logarithm
open Log


@[path]
private lemma main
  [LogPos α]
  {x y : α}
-- given
  (h₀ : x ≠ 0)
  (h₁ : y ≠ 0) :
-- imply
  log (x / y) = log x - log y :=
-- proof
  LogPos.log_div h₀ h₁


-- created on 2025-12-03
