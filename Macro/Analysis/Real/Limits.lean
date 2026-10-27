import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Syntax.Analysis.Real.Limits
open Lean
open scoped Topology


macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)

