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

/-- Count `E(P)` of horizontal `E` steps in the ordered step sequence.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountE : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountE xs + 1
  | .N :: xs => multiMarkedCountE xs
  | .marked _ _ :: xs => multiMarkedCountE xs

/-- Count `N(P)` of plain (unmarked) vertical `N` steps in the ordered step
sequence. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountPlainN : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountPlainN xs
  | .N :: xs => multiMarkedCountPlainN xs + 1
  | .marked _ _ :: xs => multiMarkedCountPlainN xs

/-- Total number of vertical steps (plain `N` plus marked `N*_t`) in the
ordered step sequence. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountVert : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedCountVert xs
  | .N :: xs => multiMarkedCountVert xs + 1
  | .marked _ _ :: xs => multiMarkedCountVert xs + 1

/-- Total number of steps in the ordered step sequence.
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountTotal : List MultiMarkedStep → Nat
  | [] => 0
  | _ :: xs => multiMarkedCountTotal xs + 1

/-- Finite sum over marked-step occurrences of their indices `t`; the exact
occurrence-level representation of the source sum `∑ t * N*_t(P)` grouped by
index. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedIndexSum : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedIndexSum xs
  | .N :: xs => multiMarkedIndexSum xs
  | .marked t _ :: xs => t + multiMarkedIndexSum xs

/-- Finite sum over marked-step occurrences of `t - 1`; the exact
occurrence-level representation of the source sum `∑ (t - 1) * N*_t(P)`
grouped by index. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedShiftedIndexSum : List MultiMarkedStep → Nat
  | [] => 0
  | .E :: xs => multiMarkedShiftedIndexSum xs
  | .N :: xs => multiMarkedShiftedIndexSum xs
  | .marked t _ :: xs => (t - 1) + multiMarkedShiftedIndexSum xs

/-- Grouped count statistic `N*_t(P)`: number of marked steps with index
exactly `t` in the ordered step sequence. Concept
`jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedCountMarkedT : List MultiMarkedStep → Nat → Nat
  | [], _ => 0
  | .marked s _ :: xs, t => (if s == t then 1 else 0) + multiMarkedCountMarkedT xs t
  | _ :: xs, t => multiMarkedCountMarkedT xs t

/-- Size of a step sequence: `E(P)` plus the occurrence sum of `t - 1` over
marked steps. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
def multiMarkedSize (l : List MultiMarkedStep) : Nat :=
  multiMarkedCountE l + multiMarkedShiftedIndexSum l

/-- A multi-marked Dyck path: an ordered finite step sequence starting at
`(0,0)` whose every prefix is underdiagonal (vertical-step count at most the
`E`-step count) and whose full path ends on the diagonal (`E` count equals
total vertical-step count). Both plain `N` and marked `N*_t` steps move
vertically by one. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
structure MultiMarkedDyckPath where
  steps : List MultiMarkedStep
  underdiagonal :
    ∀ k, k ≤ steps.length →
      multiMarkedCountVert (steps.take k) ≤ multiMarkedCountE (steps.take k)
  diagonal_endpoint : multiMarkedCountE steps = multiMarkedCountVert steps

/-- Diagonal count equality: the `E` count of a multi-marked Dyck path equals
its total vertical-step count. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedCountEq (P : MultiMarkedDyckPath) :
    multiMarkedCountE P.steps = multiMarkedCountVert P.steps :=
  P.diagonal_endpoint

/-- Occurrence-level size identity: for any step sequence, the vertical count
plus the shifted index sum equals the plain count plus the index sum (each
marked step of index `t` contributes `1 + (t - 1) = t`).
Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedVertShifted_eq (l : List MultiMarkedStep) :
    multiMarkedCountVert l + multiMarkedShiftedIndexSum l =
      multiMarkedCountPlainN l + multiMarkedIndexSum l := by
  induction l with
  | nil => rfl
  | cons hd tl ih =>
    cases hd with
    | E =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      exact ih
    | N =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega
    | marked t h =>
      simp only [multiMarkedCountVert, multiMarkedShiftedIndexSum,
        multiMarkedCountPlainN, multiMarkedIndexSum]
      omega

/-- Size equality: the size `E(P) + ∑ (t - 1) N*_t(P)` equals
`N(P) + ∑ t N*_t(P)`, derived from the diagonal endpoint via the
occurrence-level identity. Concept `jis_sem_ee7327c841ed4326952fd4fb`;
source statement `jis_54a13fcd4eb84116f24d6935`. -/
theorem multiMarkedSizeEq (P : MultiMarkedDyckPath) :
    multiMarkedSize P.steps =
      multiMarkedCountPlainN P.steps + multiMarkedIndexSum P.steps := by
  unfold multiMarkedSize
  have h := multiMarkedVertShifted_eq P.steps
  have he := multiMarkedCountEq P
  omega

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
