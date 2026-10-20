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

/-- A marked Dyck path: an underdiagonal lattice path from `(0, 0)` to the
diagonal, i.e. a step list staying weakly under the diagonal
(`E >= N + N*` on every prefix) and ending at the diagonal
(`E(P) = N(P) + N*(P)`).
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
structure MarkedDyckPath : Type where
  steps : List MarkedDyckStep
  balanced : markedDyckCountE steps = markedDyckCountN steps + markedDyckCountNstar steps
  staysUnder : ∀ n, markedDyckCountN (steps.take n) + markedDyckCountNstar (steps.take n) ≤
    markedDyckCountE (steps.take n)

/-- A step occurrence in a marked Dyck path `P` is marked (an `N*` step, as
opposed to kind `N`) iff the step at that occurrence equals `Nstar`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def IsMarkedStep (P : MarkedDyckPath) (i : Fin P.steps.length) : Prop :=
  P.steps.get i = MarkedDyckStep.Nstar

/-- Size of a marked Dyck path `P`, defined as `N*(P) + E(P)`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
def MarkedDyckPath.pathSize (P : MarkedDyckPath) : Nat :=
  markedDyckCountNstar P.steps + markedDyckCountE P.steps

/-- The size of a marked Dyck path `P` equals `N(P) + 2 * N*(P)`.
Source statement `jis_f51c1ff9625da95f812ce507`;
concept `jis_sem_1ec0710af356bb3047cb9588`. -/
theorem MarkedDyckPath.size_eq (P : MarkedDyckPath) :
    P.pathSize = markedDyckCountN P.steps + 2 * markedDyckCountNstar P.steps := by
  unfold MarkedDyckPath.pathSize
  have h := P.balanced
  omega

end MetaMathlibExt
