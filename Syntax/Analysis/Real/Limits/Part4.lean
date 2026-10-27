import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part3
open Lean
open scoped Topology


/-- `x → -∞` — x is negative infinite. -/
syntax (name := tendsToNegInf) term:26 " → " "-" "∞" : term

