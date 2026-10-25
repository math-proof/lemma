import Mathlib
import Def.TateCurve_QSeries

set_option autoImplicit false

open scoped NNReal
open IsUltrametricDist Filter

namespace TateCurve

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]


section RationalFunctions

def xfun (w : K) : K := w / (1 - w) ^ 2

def yfun (w : K) : K := w ^ 2 / (1 - w) ^ 3

end RationalFunctions

section Terms

variable (q u : K)

def xTerm (n : ℤ) : K := xfun (q ^ n * u)

def yTerm (n : ℤ) : K := yfun (q ^ n * u)

end Terms

section PointSeries

variable [CompleteSpace K] (q u : K)

noncomputable def s₁ : K := coeffSum (fun n => n) q

noncomputable def pointX : K := (∑' n : ℤ, xTerm q u n) - 2 * s₁ q

noncomputable def pointY : K := (∑' n : ℤ, yTerm q u n) + s₁ q

end PointSeries

end TateCurve
