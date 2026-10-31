import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
open Lean
open scoped Topology


/-- `x → ∞` — x is infinite. -/
syntax (name := tendsToInf) term:26 " → " "∞" : term



macro_rules (kind := tendsToInf)
  | `($x → ∞) => `(ArchimedeanClass.mk $x < 0)

/-- `x → 0` — x is infinitesimal. -/
syntax (name := tendsToZero) term:26 " → " num : term



macro_rules (kind := tendsToZero)
  | `($x → 0) => `(0 < ArchimedeanClass.mk $x)

/-- `x → +∞` — x is positive infinite. -/
syntax (name := tendsToPosInf) term:26 " → " "+" "∞" : term



macro_rules (kind := tendsToPosInf)
  | `($x → +∞) => `(0 < $x ∧ ArchimedeanClass.mk $x < 0)

/-- `x → -∞` — x is negative infinite. -/
syntax (name := tendsToNegInf) term:26 " → " "-" "∞" : term



macro_rules (kind := tendsToNegInf)
  | `($x → -∞) => `($x < 0 ∧ ArchimedeanClass.mk $x < 0)

/-- `x → 0⁺` — x is a positive infinitesimal (`0⁺`). -/
syntax (name := tendsToZeroPos) term:26 " → " num "⁺" : term



macro_rules (kind := tendsToZeroPos)
  | `($x → 0⁺) => `(0 < $x ∧ 0 < ArchimedeanClass.mk $x)

/-- `x → 0⁻` — x is a negative infinitesimal (`0⁻`). -/
syntax (name := tendsToZeroNeg) term:26 " → " num "⁻" : term



macro_rules (kind := tendsToZeroNeg)
  | `($x → 0⁻) => `($x < 0 ∧ 0 < ArchimedeanClass.mk $x)

/-- Point in `lim [x → x₀]`, `lim [x → x₀⁺]`, `lim [x → x₀⁻]`.
`ident` covers `x₀`; `num` covers `0`. Kept off `term` so `⁺` / `⁻` are not parsed as `posPart` / `negPart`. -/
declare_syntax_cat limPt
syntax ident : limPt

syntax num : limPt
