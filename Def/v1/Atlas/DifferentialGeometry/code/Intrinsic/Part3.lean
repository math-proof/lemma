/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialGeometry/code/Intrinsic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Def.v1.Atlas.DifferentialGeometry.code.Hypersurfaces
public import Theorem.Real.Atlas.v1.DifferentialGeometry.code.Hypersurfaces
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Tactic.NoncommRing
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Abbrev.v1.Atlas.DifferentialGeometry.code.Intrinsic

@[expose] public section

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
