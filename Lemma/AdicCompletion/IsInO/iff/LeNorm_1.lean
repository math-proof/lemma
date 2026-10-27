import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.AdicCompletion.Support.DVRPadic

open AdicCompletionSupport

/--
[padic_isInO_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/DVRInstances.lean)
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
  (padicDVRContext p n hn).isInO x ↔ ‖x‖ ≤ 1 := by
-- proof
  apply padic_isInO_iff n hn x


-- created on 2026-10-23
