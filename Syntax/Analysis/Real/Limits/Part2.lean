import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits
open Lean
open scoped Topology


/-- `x → 0` — x is infinitesimal. -/
syntax (name := tendsToZero) term:26 " → " num : term

