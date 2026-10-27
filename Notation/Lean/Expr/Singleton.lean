import Def.Lean.Name
import Mathlib.Basic.Real.Basic
import Def.Lean.Expr.Singleton.Part2
open Lean


notation "ℝ⁺" => { x : ℝ // 0 < x }

notation "ℝ⁻" => { x : ℝ // x < 0 }

