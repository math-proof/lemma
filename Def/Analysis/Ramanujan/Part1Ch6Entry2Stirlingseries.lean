/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry2Stirlingseries.lean -/

/-
Author: @akiezun, Avocado
-/

module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Def.Analysis.SpecialFunctions.Gamma.Digamma
public import Theorem.Complex.Digamma
public import Theorem.Real.Digamma
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Set

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 2

Away from the negative integers, `ψ(z+1) + γ` is complex differentiable and its derivative is
the absolutely convergent series `∑ 1/(z+k+1)²`. The general Gamma and digamma facts used here
live in `MathlibExt.Analysis.SpecialFunctions.Gamma.Digamma`.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry2Stirlingseries

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter6HarmonicInterpolation (z : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) +
    deriv Complex.Gamma (z + 1) / Complex.Gamma (z + 1)

/-- Right half-plane. -/
def H : Set ℂ := {z | 0 < z.re}

/-- Trigamma summand. -/
def triTerm (k : ℕ) (w : ℂ) : ℂ := 1 / (w + ((k + 1 : ℕ) : ℂ)) ^ 2

/-- Interpolation function (unfolded). -/
def Jfun (w : ℂ) : ℂ :=
  (Real.eulerMascheroniConstant : ℂ) + deriv Complex.Gamma (w + 1) / Complex.Gamma (w + 1)

end
end Entry2Stirlingseries
end MathlibExt.Analysis.Ramanujan.Part1Ch6
