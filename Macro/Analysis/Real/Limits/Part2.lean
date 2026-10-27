import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part2
open Lean
open scoped Topology


macro_rules (kind := tendsToZero)
  | `($x → 0) => `(0 < ArchimedeanClass.mk $x)

