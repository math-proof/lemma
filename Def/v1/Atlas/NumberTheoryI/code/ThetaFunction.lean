/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/ThetaFunction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.Complex.Periodic
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.Real.Pi.Bounds
open Complex Filter Asymptotics Function Set
open scoped Real Topology


noncomputable section

noncomputable def mkQuotient (h : ℂ → ℂ) (z : ℂ) : ℂ :=
  if Complex.sin ((↑Real.pi : ℂ) * z) = 0 then
    dslope h ↑(⌊z.re⌋ : ℤ) z /
      dslope (fun w => Complex.sin ((↑Real.pi : ℂ) * w)) ↑(⌊z.re⌋ : ℤ) z
  else h z / Complex.sin ((↑Real.pi : ℂ) * z)

end
