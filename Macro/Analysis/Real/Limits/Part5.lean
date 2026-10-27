import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part5
open Lean
open scoped Topology


macro_rules (kind := tendsToZeroPos)
  | `($x → 0⁺) => `(0 < $x ∧ 0 < ArchimedeanClass.mk $x)

