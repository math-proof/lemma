import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Topology.Defs.Filter
import Macro.Analysis.Real.Limits.Part7
open Lean
open scoped Topology


/-- Point in `lim [x → x₀]`, `lim [x → x₀⁺]`, `lim [x → x₀⁻]`.
`ident` covers `x₀`; `num` covers `0`. Kept off `term` so `⁺` / `⁻` are not parsed as `posPart` / `negPart`. -/
declare_syntax_cat limPt
syntax ident : limPt

syntax num : limPt

