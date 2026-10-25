/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch8Entry15Doublegamma.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @akiezun, Avocado, Codex
-/

import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Def.Analysis.SpecialFunctions.Gamma.Digamma
import Lemma.Complex.Digamma
import Lemma.Real.Digamma
/-!
# Ramanujan's centered digamma asymptotic

This file proves the sixth-order centered digamma expansion and uses it to derive Ramanujan's
eighth-order asymptotic formula for a complex power of `(x + 1 / 2) / exp (ψ (x + 1))`.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch8

namespace Entry15Doublegamma

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter8RealDigamma (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

def ch8Entry15_logTaylor (u : ℝ) : ℝ :=
  u - u ^ 2 / 2 + u ^ 3 / 3 - u ^ 4 / 4 + u ^ 5 / 5 - u ^ 6 / 6 +
    u ^ 7 / 7 - u ^ 8 / 8

def ch8Entry15_rationalStep (u : ℝ) : ℝ :=
  u / (1 + u / 2) + 1 / 24 * (u ^ 2 - u ^ 2 / (1 + u) ^ 2) -
    7 / 960 * (u ^ 4 - u ^ 4 / (1 + u) ^ 4) +
    31 / 8064 * (u ^ 6 - u ^ 6 / (1 + u) ^ 6)

def ch8Entry15_rationalNumerator (u : ℝ) : ℝ :=
  1661 / 5760 + 793 / 576 * u + 5719 / 1920 * u ^ 2 + 2561 / 720 * u ^ 3 +
    19375 / 8064 * u ^ 4 + 6 / 7 * u ^ 5 + 1 / 8 * u ^ 6

def ch8Entry15_remainder (y : ℝ) : ℝ :=
  chapter8RealDigamma (y + 1 / 2) - Real.log y - 1 / (24 * y ^ 2) +
    7 / (960 * y ^ 4) - 31 / (8064 * y ^ 6)

def ch8Entry15_step (y : ℝ) : ℝ :=
  ch8Entry15_remainder y - ch8Entry15_remainder (y + 1)

def chapter8Entry15A (x : ℝ) : ℝ :=
  Real.exp (chapter8RealDigamma (x + 1))

def chapter8Entry15Approx (n : ℂ) (x : ℝ) : ℂ :=
  let a : ℂ := chapter8Entry15A x
  1 - n / (6 * a ^ 2) + (10 * n ^ 2 + 11 * n) / (720 * a ^ 4) -
    (70 * n ^ 3 + 231 * n ^ 2 + 891 * n) / (90720 * a ^ 6)

def chapter8Entry15Power (n : ℂ) (x : ℝ) : ℂ :=
  Complex.cpow ((((x + 1 / 2) / chapter8Entry15A x : ℝ) : ℂ)) (4 * n)

def ch8Entry15Q (x : ℝ) : ℂ :=
  ((1 / (x + 1 / 2) ^ 2 : ℝ) : ℂ)

def ch8Entry15D (x : ℝ) : ℂ :=
  ((chapter8RealDigamma (x + 1) - Real.log (x + 1 / 2) : ℝ) : ℂ)

def ch8Entry15P (x : ℝ) : ℂ :=
  ((1 / (24 * (x + 1 / 2) ^ 2) - 7 / (960 * (x + 1 / 2) ^ 4) +
    31 / (8064 * (x + 1 / 2) ^ 6) : ℝ) : ℂ)

def ch8Entry15S (x : ℝ) : ℂ :=
  ch8Entry15Q x * Complex.exp (-2 * ch8Entry15D x)

def ch8Entry15Cubic (c z : ℂ) : ℂ :=
  1 + c * z + (c * z) ^ 2 / 2 + (c * z) ^ 3 / 6

def ch8Entry15ExpPoly (c : ℂ) (x : ℝ) : ℂ :=
  let q := ch8Entry15Q x
  1 + (c / 24) * q + (-7 * c / 960 + c ^ 2 / (2 * 24 ^ 2)) * q ^ 2 +
    (31 * c / 8064 - 7 * c ^ 2 / (24 * 960) + c ^ 3 / (6 * 24 ^ 3)) * q ^ 3

def ch8Entry15CubicDiffFactor (c : ℂ) (x : ℝ) : ℂ :=
  c + c ^ 2 / 2 * (ch8Entry15D x + ch8Entry15P x) +
    c ^ 3 / 6 * (ch8Entry15D x ^ 2 + ch8Entry15D x * ch8Entry15P x +
      ch8Entry15P x ^ 2)

def ch8Entry15SPoly (x : ℝ) : ℂ :=
  ch8Entry15Q x - ch8Entry15Q x ^ 2 / 12 + 13 * ch8Entry15Q x ^ 3 / 720

def ch8Entry15ApproxS (n : ℂ) (x : ℝ) : ℂ :=
  1 - n / 6 * ch8Entry15S x + (10 * n ^ 2 + 11 * n) / 720 * ch8Entry15S x ^ 2 -
    (70 * n ^ 3 + 231 * n ^ 2 + 891 * n) / 90720 * ch8Entry15S x ^ 3

end
end Entry15Doublegamma
end MathlibExt.Analysis.Ramanujan.Part1Ch8
