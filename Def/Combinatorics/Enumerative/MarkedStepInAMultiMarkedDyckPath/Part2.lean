/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic
import Structure.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath


namespace MetaMathlibExt

/-- Vertical-step test used to delimit the final run of vertical steps.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedIsVert : MultiMarkedStep → Bool
  | .E => false
  | .N => true
  | .marked _ _ => true

/-- Final (trailing) run of vertical steps: the suffix after the last `E`
step, or the whole sequence if there is no `E` step.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedTrailingVert (l : List MultiMarkedStep) : List MultiMarkedStep :=
  (l.reverse.takeWhile multiMarkedIsVert).reverse

/-- A marked tail: the final run of vertical steps contains at least one
marked `N*_t` step. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPath.HasMarkedTail (P : MultiMarkedDyckPath) : Prop :=
  ∃ (t : Nat) (h : 2 ≤ t),
    MultiMarkedStep.marked t h ∈ multiMarkedTrailingVert P.steps

/-- An unmarked tail: the final run of vertical steps contains no marked
step. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPath.HasUnmarkedTail (P : MultiMarkedDyckPath) : Prop :=
  ¬ P.HasMarkedTail

/-- The set `P̃_n` of multi-marked Dyck paths of size `n`.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedDyckPathOfSize (n : Nat) : Type :=
  { P : MultiMarkedDyckPath // multiMarkedSize P.steps = n }

/-- The set `R̃_n` of size-`n` multi-marked Dyck paths with an unmarked tail.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def MultiMarkedUnmarkedTail (n : Nat) : Type :=
  { P : MultiMarkedDyckPath //
    multiMarkedSize P.steps = n ∧ P.HasUnmarkedTail }

end MetaMathlibExt
