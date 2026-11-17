/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ThetaFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Liouville
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.Complex.RemovableSingularity
public import Mathlib.Analysis.Complex.PhragmenLindelof
public import Mathlib.Analysis.Complex.Periodic
public import Mathlib.Analysis.Analytic.IsolatedZeros
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Analysis.Real.Pi.Bounds

@[expose] public section

open Complex Filter Asymptotics Function Set
open scoped Real Topology


noncomputable section

noncomputable def mkQuotient (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if Complex.sin ((↑Real.pi : ℂ) * z) = 0 then
    dslope h ↑(⌊z.re⌋ : ℤ) z /
      dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) ↑(⌊z.re⌋ : ℤ) z
  else h z / Complex.sin ((↑Real.pi : ℂ) * z)

end
