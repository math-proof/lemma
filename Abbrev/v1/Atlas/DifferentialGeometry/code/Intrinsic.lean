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
public import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part2


@[expose] public noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace ChristoffelFromMetric

open ChristoffelSymbols

abbrev AntisymIndex (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

end ChristoffelFromMetric
end ChristoffelSymbols
end
