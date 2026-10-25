/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/CPythonListsort/Code/Policy/StackPowers.lean -/

import Def.CPythonListsort.Code.Policy.PendingLayout
import Def.CPythonListsort.Code.Transcription.Powerloop
import Mathlib.Data.List.Pairwise
import Def.CPythonListsort.Code.Policy.StackPowers
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

end CPythonListsort
