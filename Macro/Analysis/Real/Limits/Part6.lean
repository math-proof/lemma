import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part6
open Lean
open scoped Topology


macro_rules (kind := tendsToZeroNeg)
  | `($x → 0⁻) => `($x < 0 ∧ 0 < ArchimedeanClass.mk $x)

