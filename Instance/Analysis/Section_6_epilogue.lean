import Mathlib
import Theorem.Analysis.Section_6_7.Part2
import Theorem.Analysis.Section_6_epilogue
open Filter

/-!
# Analysis I, Chapter 6 epilogue: Connections with Mathlib limits

In this (technical) epilogue, we show that various operations and properties we have defined for
"Chapter 6" sequences {name}`Chapter6.Sequence` are equivalent to Mathlib operations.  Note however
that Mathlib's operations are defined in far greater generality than the setting of real-valued
sequences, in particular using the language of filters.

-/


/-- A technicality: {name}`CauSeq.IsComplete` {lean}`ℝ` was established for {name}`_root_.abs` but not for {name}`norm`. -/
instance inst_real_complete : CauSeq.IsComplete ℝ norm := by convert Real.instIsCompleteAbs

