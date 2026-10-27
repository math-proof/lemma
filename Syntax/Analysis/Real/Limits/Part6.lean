import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part5
open Lean
open scoped Topology


/-- `x → 0⁻` — x is a negative infinitesimal (`0⁻`). -/
syntax (name := tendsToZeroNeg) term:26 " → " num "⁻" : term

