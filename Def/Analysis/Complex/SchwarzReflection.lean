module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.HasPrimitives
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

@[expose] public section

namespace Complex.SchwarzReflection

section

/-- The Schwarz reflected extension of `f`: equal to `f` on the closed upper
half-plane, and the conjugate reflection below the real axis. -/
noncomputable def schwarzExt (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => if 0 ≤ z.im then f z else star (f (star z))

end
end Complex.SchwarzReflection
