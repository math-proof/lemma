/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/WeightedHilbert.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Normed.Group.AddCircle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic
/-!
# Weighted Hilbert inequality

The weighted cosecant form used in the Montgomery–Vaughan proof of the
Brun–Titchmarsh theorem.
-/


namespace MathlibExt.NumberTheory.PrimeCounting

open Set MeasureTheory

noncomputable def cscSq (y : ℝ) : ℝ :=
  1 / Real.sin (Real.pi * y) ^ 2

noncomputable def cscSqDeriv (y : ℝ) : ℝ :=
  -2 * Real.pi * Real.cos (Real.pi * y) / Real.sin (Real.pi * y) ^ 3

noncomputable def cscSqDeriv2 (y : ℝ) : ℝ :=
  2 * Real.pi ^ 2 * (1 + 2 * Real.cos (Real.pi * y) ^ 2) /
    Real.sin (Real.pi * y) ^ 4

noncomputable def cscSqProduct (a y : ℝ) : ℝ :=
  cscSq y * cscSq (y - a)

noncomputable def cscSqProductDeriv (a y : ℝ) : ℝ :=
  cscSqDeriv y * cscSq (y - a) + cscSq y * cscSqDeriv (y - a)

noncomputable def cscSqProductDeriv2 (a y : ℝ) : ℝ :=
  cscSqDeriv2 y * cscSq (y - a) +
    2 * cscSqDeriv y * cscSqDeriv (y - a) +
    cscSq y * cscSqDeriv2 (y - a)

noncomputable def cotPi (y : ℝ) : ℝ :=
  Real.cos (Real.pi * y) / Real.sin (Real.pi * y)

noncomputable def logAbsSinPi (y : ℝ) : ℝ :=
  Real.log |Real.sin (Real.pi * y)|

noncomputable def cscSqProductAnti (a y : ℝ) : ℝ :=
  cscSq a / Real.pi *
    (-cotPi y - cotPi (y - a) +
      2 * cotPi a * (logAbsSinPi y - logAbsSinPi (y - a)))

noncomputable def cscSqAnti (y : ℝ) : ℝ :=
  -Real.cos (Real.pi * y) / (Real.pi * Real.sin (Real.pi * y))

noncomputable def circleCoord {ι : Type*} (x : ι → ℝ) (s r : ι) : ℝ :=
  (AddCircle.equivIco (1 : ℝ) 0
    ((x r - x s : ℝ) : AddCircle (1 : ℝ))).1

noncomputable def weightedMatrix {ι : Type*} (δ : ι → ℝ)
    (K : ι → ι → ℝ) : Matrix ι ι ℂ :=
  fun r s ↦ Complex.I * Real.sqrt (δ r) * Real.sqrt (δ s) * K r s

noncomputable def cosecantKernel {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else 1 / Real.sin (Real.pi * (x r - x s))

noncomputable def cotangentKernel {ι : Type*} [DecidableEq ι]
    (x : ι → ℝ) (r s : ι) : ℝ :=
  if r = s then 0 else
    Real.cos (Real.pi * (x r - x s)) / Real.sin (Real.pi * (x r - x s))

end MathlibExt.NumberTheory.PrimeCounting
