import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[padic_isUnitInO_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
-/
@[path]
private lemma main
  {p : ℕ}
  [Fact (Nat.Prime p)]
  {n : ℕ}
  {x : ℚ_[p]}
-- given
  (hn : 0 < n) :
-- imply
  (padicDVRContext p n hn).isUnitInO x ↔ ‖x‖ = 1 := by
-- proof
  apply padic_isUnitInO_iff n hn x


-- created on 2026-10-23
