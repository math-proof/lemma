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
import Abbrev.v1.Atlas.DifferentialGeometry.code.Intrinsic


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace ChristoffelFromMetric

open ChristoffelSymbols

noncomputable def exteriorPowerShapeOpMatrix_antisym (patch : HypersurfacePatch n)
    (x : Fin n → ℝ) : Matrix (AntisymIndex n) (AntisymIndex n) ℝ :=
  Matrix.of (fun p q => exteriorPowerShapeOp patch x p.val.1 p.val.2 q.val.1 q.val.2)

def riemannCurvature (patch : HypersurfacePatch 2)
    (x : Fin 2 → ℝ) (i j k s : Fin 2) : ℝ :=
  GaussEquation.riemannCurvature patch x i j k s

end ChristoffelFromMetric
end ChristoffelSymbols
end
