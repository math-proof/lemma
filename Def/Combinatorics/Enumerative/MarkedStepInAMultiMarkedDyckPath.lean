/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MarkedStepInAMultiMarkedDyckPath.lean -/

import Mathlib.Data.List.Basic
import Inductive.Combinatorics.Enumerative.MarkedStepInAMultiMarkedDyckPath


namespace MetaMathlibExt

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

end MetaMathlibExt
