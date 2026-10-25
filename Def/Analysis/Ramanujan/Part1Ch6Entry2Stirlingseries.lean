/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch6Entry2Stirlingseries.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Def.Analysis.SpecialFunctions.Gamma.Digamma
import Lemma.Complex.Digamma
import Lemma.Real.Digamma
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Set
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
