/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.WLOG


namespace MetaMathlibExt

/-- Eventually periodic sequence (concept `jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `definition`):
a sequence `u : ℕ → α` admitting a positive period `p` and a preperiod `n₀`
with `u (n + p) = u n` for every `n ≥ n₀`. -/
def IsEventuallyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  ∃ p n₀ : ℕ, 0 < p ∧ ∀ n : ℕ, n₀ ≤ n → u (n + p) = u n

end MetaMathlibExt
