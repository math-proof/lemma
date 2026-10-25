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
import Def.v1.Atlas.DifferentialGeometry.code.Intrinsic.Part2


noncomputable section

open Matrix Finset BigOperators

variable {n : ℕ}

namespace ChristoffelSymbols

namespace ChristoffelFromMetric

open ChristoffelSymbols

abbrev AntisymIndex (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

end ChristoffelFromMetric
end ChristoffelSymbols
end
