import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Def.Analysis.Real.Limits
open Lean
open scoped Topology


/-- `x → +∞` — x is positive infinite. -/
syntax (name := tendsToPosInf) term:26 " → " "+" "∞" : term

