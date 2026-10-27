import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits.Part4
open Lean
open scoped Topology


macro_rules (kind := tendsToNegInf)
  | `($x → -∞) => `($x < 0 ∧ ArchimedeanClass.mk $x < 0)

