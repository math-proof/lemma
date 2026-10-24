/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean -/

import sympy.atlas.CPythonListsort.Code.Policy.PendingLayout
import sympy.atlas.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Data.List.Pairwise

/-!
# Pending-stack power invariants

The pending array is unbounded in the Lean model.  This module records the
PowerSort policy facts from CPython: every stored boundary label is exactly the
result of the transcribed `powerloop` on the adjacent runs' current geometry,
and powers on older runs strictly increase in C array order and lie in the
concrete interval `1 .. 60`.  There is deliberately no
`MAX_MERGE_PENDING` guard in either invariant.
-/

namespace CPythonListsort

universe u v

/-- The exact node power belonging to the boundary between two adjacent
pending runs.  `left.base - basekeys` is CPython's `s1`; the remaining
arguments are the two current run lengths and the original list length. -/
def pendingBoundaryPower (basekeys : Nat) (listlen : PySSize)
    (left right : PendingRun) : Nat :=
  powerloop (BitVec.ofNat 64 (left.base - basekeys)) left.len right.len listlen

/-- Every left endpoint of an adjacent pending-run pair stores exactly the
power computed from that pair's current geometry.  The final run has no
outgoing boundary, so its stored field is deliberately unconstrained. -/
def ExactBoundaryPowers (basekeys : Nat) (listlen : PySSize) :
    List PendingRun → Prop
  | [] => True
  | [_] => True
  | left :: right :: rest =>
      left.power = some (pendingBoundaryPower basekeys listlen left right) ∧
        ExactBoundaryPowers basekeys listlen (right :: rest)

/-- A list of pending runs has initialized, strictly increasing powers in the
concrete range produced by `powerloop`.  The witness list follows C array
order, so its head is the oldest pending run. -/
def IncreasingPendingPowers (runs : List PendingRun) : Prop :=
  ∃ powers : List Nat,
    runs.map PendingRun.power = powers.map some ∧
      (∀ power ∈ powers, 1 ≤ power ∧ power ≤ 60) ∧
      powers.Pairwise (· < ·)

/-- Steady-state PowerSort invariant, immediately after a run is pushed.

The empty stack is valid.  On every nonempty stack there is exactly one newest
run, whose stored `power` field is deliberately unconstrained because
CPython's push writes only its base and length.  Every older run's stored power
is exactly the transcribed `powerloop` result for its boundary with the next
run, lies in `1 .. 60`, and increases strictly in C array order.  Consequently
the condition is vacuous for a singleton stack. -/
def PoweredPrefix (state : MergeState κ ν) : Prop :=
  state.pending.toList = [] ∨
    ∃ olderRuns newest,
      state.pending.toList = olderRuns ++ [newest] ∧
        IncreasingPendingPowers olderRuns ∧
        ExactBoundaryPowers state.basekeys state.listlen state.pending.toList

/-- Facts about a newly discovered run before the caller's unconditional
`Array.push`.  The current pending stack still covers exactly `scanned`
entries, all of its runs are powered, and `newRun` is the adjacent nonempty
run just outside that stack.  Its stored `power` field is irrelevant, matching
the C push, which writes only base and length.  The exact-boundary predicate is
stated on the virtual post-push list, so it also pins the current top run's
stored power to the boundary with `newRun`.  No array-capacity premise is
present. -/
def ReadyToPush (state : MergeState κ ν) (scanned : Nat)
    (newRun : PendingRun) : Prop :=
  PendingLayout state scanned ∧
    IncreasingPendingPowers state.pending.toList ∧
    ExactBoundaryPowers state.basekeys state.listlen
      (state.pending.toList ++ [newRun]) ∧
    newRun.base = state.basekeys + scanned ∧
    newRun.len.Nonnegative ∧
    0 < newRun.len.toNat ∧
    scanned + newRun.len.toNat ≤ state.listlen.toNat ∧
    newRun ∉ state.pending.toList

/-- A singleton steady-state stack is valid regardless of its stale or
uninitialized stored power. -/
example (state : MergeState κ ν) (run : PendingRun) :
    PoweredPrefix { state with pending := #[run] } := by
  exact poweredPrefix_singleton state run

/-- Two unpowered runs are invalid: only the unique newest run may lack a
power. -/
example (state : MergeState κ ν) (older newest : PendingRun)
    (holder : older.power = none) (_hnewest : newest.power = none) :
    ¬PoweredPrefix { state with pending := #[older, newest] } := by
  intro h
  rcases h with hempty | ⟨olderRuns, top, hsplit, hpowers, _hexact⟩
  · simp at hempty
  · have hsplit' : [older, newest] = olderRuns ++ [top] := by simpa using hsplit
    have holderRunsLength : olderRuns.length = 1 := by
      have := congrArg List.length hsplit'
      simp only [List.length_cons, List.length_nil, List.length_append] at this
      omega
    obtain ⟨only, rfl⟩ := List.length_eq_one_iff.mp holderRunsLength
    simp only [List.singleton_append, List.cons.injEq] at hsplit'
    have honly := hpowers.run_power (run := only) (by simp)
    rcases honly with ⟨power, hsome, _⟩
    have hsomeOlder : older.power = some power := by
      simpa [hsplit'.1] using hsome
    rw [holder] at hsomeOlder
    simp at hsomeOlder

private def mislabeledOlder : PendingRun :=
  { base := 0, len := 1, power := some 2 }

private def unlabeledNewest : PendingRun :=
  { base := 1, len := 1, power := none }
