import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part3
open Lean
open scoped Topology


macro_rules (kind := tendsToPosInf)
  | `($x → +∞) => `(0 < $x ∧ ArchimedeanClass.mk $x < 0)

