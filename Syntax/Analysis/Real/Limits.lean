import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
open Lean
open scoped Topology


/-- `x → ∞` — x is infinite. -/
syntax (name := tendsToInf) term:26 " → " "∞" : term



macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)
