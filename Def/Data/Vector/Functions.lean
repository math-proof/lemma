import Instance.Data.Vector.Vector
import Instance.Analysis.SpecialFunctions.Exponential.Part5
import Def.Analysis.SpecialFunctions.Trigonometric.Part2
import Theorem.Analysis.Real.Relational
open Vector


namespace List.Vector

/--
Elementwise sine. Available for `Vector ℝ n` and `Vector ℂ n` via `Sin`.
-/
def sin [Sin α] (x : Vector α n) : Vector α n :=
  x.map Sin.sin

/--
Elementwise cosine. Available for `Vector ℝ n` and `Vector ℂ n` via `Cos`.
-/
def cos [Cos α] (x : Vector α n) : Vector α n :=
  x.map Cos.cos

/--
Elementwise cotangent. Available for `Vector ℝ n` and `Vector ℂ n` via `Cot`.
-/
def cot [Cot α] (x : Vector α n) : Vector α n :=
  x.map Cot.cot

/--
Elementwise tangent. Available for `Vector ℝ n` and `Vector ℂ n` via `Tan`.
-/
def tan [Tan α] (x : Vector α n) : Vector α n :=
  x.map Tan.tan

end List.Vector
