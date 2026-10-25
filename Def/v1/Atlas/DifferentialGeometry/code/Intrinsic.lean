/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
import Lemma.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Tactic.NoncommRing
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

def secondPartialDeriv (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j : Fin n) : Fin (n + 1) → ℝ :=
  fderiv ℝ (fun y => fderiv ℝ patch.f y (Pi.single j 1)) x (Pi.single i 1)

noncomputable def christoffelSymbol (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) (i j k : Fin n) : ℝ :=
  let G := firstFundamentalForm patch x
  let d2f := secondPartialDeriv patch x i j
  let tangentialCoeffs : Fin n → ℝ := fun l => d2f ⬝ᵥ (patch.partialDeriv x l)
  ((G⁻¹) *ᵥ tangentialCoeffs) k

noncomputable def partialDeriv {n : ℕ} (i : Fin n) (g : (Fin n → ℝ) → ℝ)
    (x : Fin n → ℝ) : ℝ :=
  fderiv ℝ g x (Pi.single i 1)

namespace ChristoffelFromMetric

open ChristoffelSymbols

noncomputable def tensorT (S : ι → ι → ι → F) (i j k : ι) : F :=
  (S i j k + S j k i - S k i j) / 2

end ChristoffelFromMetric
end ChristoffelSymbols
end
