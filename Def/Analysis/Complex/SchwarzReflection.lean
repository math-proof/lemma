import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring


namespace Complex.SchwarzReflection

section

/-- The Schwarz reflected extension of `f`: equal to `f` on the closed upper
half-plane, and the conjugate reflection below the real axis. -/
noncomputable def schwarzExt (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if 0 ≤ z.im then f z else star (f (star z))

end
end Complex.SchwarzReflection
