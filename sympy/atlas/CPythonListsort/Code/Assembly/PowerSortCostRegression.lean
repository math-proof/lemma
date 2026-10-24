/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Assembly/PowerSortCostRegression.lean -/

import sympy.atlas.CPythonListsort.Code.Assembly.ListSortMergePolicy
import sympy.atlas.CPythonListsort.Code.Assembly.PowerSortPolicyCost

/-!
# Executable regression for the PowerSort cost bridge

This module contains one large, compiler-checked review witness.  It exercises
the real top-level evaluator on seven ascending natural runs separated by
strict drops.  The resulting adaptive formed-run partition is the concrete
counterexample showing why CPython's final-collapse tree must be compared by
cost, rather than identified with Algorithm 2's canonical tree.

The witness is never consumed by another Lean declaration.  Its compiler-side
evaluation trust boundary is listed in the project-wide ledger.
-/

namespace CPythonListsort

private def costRegressionBlock (length : Nat) :
    List (SortSliceEntry Nat Unit) :=
  (List.range length).map fun key => { key := key, value := none }

private def costRegressionRunLengths : List Nat :=
  [32, 33, 83, 36, 32, 32, 8]

private def powerSortCostRegressionInput : SortSlice Nat Unit :=
  { entries :=
      (costRegressionRunLengths.flatMap costRegressionBlock).toArray }

private def powerSortCostRegressionTrace : List PolicyEvent :=
  (listSortImplTraced? (fun left right : Nat => decide (left < right))
    false false powerSortCostRegressionInput).trace.policyEvents

private def policyBoundaryPowers (input : RunSpan) :
    List RunSpan → List Nat
  | left :: right :: rest =>
      replayBoundaryPower input left right ::
        policyBoundaryPowers input (right :: rest)
  | _ => []

private def powerSortCostRegressionScanEvents : List PolicyEvent :=
  [.formed
      { run := { base := 0, len := 32 }
        depthAfter := 1
        naturalLength := 32
        target := 32
        remainingBefore := 256 },
    .formed
      { run := { base := 32, len := 33 }
        depthAfter := 2
        naturalLength := 33
        target := 32
        remainingBefore := 224 },
    .merge
      { index := 0
        left := { base := 0, len := 32 }
        right := { base := 32, len := 33 } },
    .formed
      { run := { base := 65, len := 83 }
        depthAfter := 2
        naturalLength := 83
        target := 32
        remainingBefore := 191 },
    .merge
      { index := 0
        left := { base := 0, len := 65 }
        right := { base := 65, len := 83 } },
    .formed
      { run := { base := 148, len := 36 }
        depthAfter := 2
        naturalLength := 36
        target := 32
        remainingBefore := 108 },
    .formed
      { run := { base := 184, len := 32 }
        depthAfter := 3
        naturalLength := 32
        target := 32
        remainingBefore := 72 },
    .formed
      { run := { base := 216, len := 32 }
        depthAfter := 4
        naturalLength := 32
        target := 32
        remainingBefore := 40 },
    .formed
      { run := { base := 248, len := 8 }
        depthAfter := 5
        naturalLength := 8
        target := 32
        remainingBefore := 8 }]

private def powerSortCostRegressionCollapseEvents : List PolicyEvent :=
  [.merge
      { index := 3
        left := { base := 216, len := 32 }
        right := { base := 248, len := 8 } },
    .merge
      { index := 1
        left := { base := 148, len := 36 }
        right := { base := 184, len := 32 } },
    .merge
      { index := 1
        left := { base := 148, len := 68 }
        right := { base := 216, len := 40 } },
    .merge
      { index := 0
        left := { base := 0, len := 148 }
        right := { base := 148, len := 108 } }]
