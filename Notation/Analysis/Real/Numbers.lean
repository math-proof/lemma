import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Hyperreal
import Mathlib.Basic.ENNReal.Real
import Abbrev.Analysis.Real.Numbers
export Complex (I)


notation "∞" => Hyperreal.omega

notation "ℝ⁺" => { x : ℝ // 0 < x }

notation "ℝ⁻" => { x : ℝ // x < 0 }
