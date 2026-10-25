/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic


namespace MetaMathlibExt

/-- Ordered steps of a multi-marked Dyck path: horizontal `E = (1,0)`, plain
vertical `N = (0,1)`, and marked vertical steps `N*_t = (0,1)` whose index
`t >= 2` is carried with its proof, so invalid marked steps cannot be
constructed. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
inductive MultiMarkedStep where
  | E : MultiMarkedStep
  | N : MultiMarkedStep
  | marked : (t : Nat) → 2 ≤ t → MultiMarkedStep

end MetaMathlibExt
