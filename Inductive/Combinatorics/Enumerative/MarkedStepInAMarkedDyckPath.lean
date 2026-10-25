/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
/-!
# Marked step in a marked Dyck path

Formalizes the required clauses for the concept "marked step in a marked Dyck
path" (alias: N* step): in a marked Dyck path `P`, a marked step is a vertical
step of kind `N*` (as opposed to kind `N`); with `E(P)`, `N(P)`, `N*(P)` the
numbers of `E`, `N` and `N*` steps, the size of `P` is
`N*(P) + E(P) = N(P) + 2 * N*(P)`.

Source: Sergi Elizalde, *Patterns in Inversion Sequences II*:
<https://cs.uwaterloo.ca/journals/JIS/VOL22/Elizalde/eli14.tex>.
-/


namespace MetaMathlibExt

/-- Step kinds occurring in a marked Dyck path: horizontal step `E = (1, 0)`
and the two kinds of vertical steps `(0, 1)`, unmarked `N` and marked `N*`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
inductive MarkedDyckStep : Type where
  | E : MarkedDyckStep
  | N : MarkedDyckStep
  | Nstar : MarkedDyckStep

end MetaMathlibExt
