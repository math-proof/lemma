/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic
import Lean.Elab.Tactic.Omega
import Inductive.Combinatorics.Enumerative.MarkedStepInAMarkedDyckPath
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

/-- Number `E(P)` of horizontal `E` steps in a step list `P`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountE : List MarkedDyckStep → Nat
  | [] => 0
  | .E :: t => markedDyckCountE t + 1
  | _ :: t => markedDyckCountE t

/-- Number `N(P)` of unmarked vertical `N` steps in a step list `P`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountN : List MarkedDyckStep → Nat
  | [] => 0
  | .N :: t => markedDyckCountN t + 1
  | _ :: t => markedDyckCountN t

/-- Number `N*(P)` of marked vertical `N*` steps in a step list `P`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def markedDyckCountNstar : List MarkedDyckStep → Nat
  | [] => 0
  | .Nstar :: t => markedDyckCountNstar t + 1
  | _ :: t => markedDyckCountNstar t

end MetaMathlibExt
