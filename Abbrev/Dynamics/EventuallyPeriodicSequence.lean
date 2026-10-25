/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Dynamics/EventuallyPeriodicSequence.lean -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.WLOG
import Def.Dynamics.EventuallyPeriodicSequence


namespace MetaMathlibExt

/-- Ultimately periodic is terminology for the same concept (concept
`jis_sem_2c65b9e5cf5a27c75318c558`;
source statements `jis_2541b4a8b30e59c04cfc2cab`, `jis_6271663997522001b37d9cd0`,
`jis_7be4cb01363efa6d047e19af`, `jis_9f6420ee91649658b50a752a`, clause `alias`):
recorded here as an abbreviation so its semantics are not duplicated. -/
abbrev IsUltimatelyPeriodic {α : Type _} (u : ℕ → α) : Prop :=
  IsEventuallyPeriodic u

end MetaMathlibExt
