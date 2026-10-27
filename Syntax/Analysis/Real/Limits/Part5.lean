import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part4
open Lean
open scoped Topology


/-- `x → 0⁺` — x is a positive infinitesimal (`0⁺`). -/
syntax (name := tendsToZeroPos) term:26 " → " num "⁺" : term

