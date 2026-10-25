/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Combinatorics.SimpleGraph.Prod
import Mathlib.Combinatorics.SimpleGraph.Circulant
import Mathlib.Combinatorics.SimpleGraph.LapMatrix
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic


namespace SimpleGraph

variable {V : Type*} {W : Type*}

abbrev cartesianProduct (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) :=
  G □ H

end SimpleGraph

namespace SpectraCommonGraphs

open Real SimpleGraph Matrix

noncomputable section

abbrev ringGraph (n : ℕ) : SimpleGraph (Fin n) := SimpleGraph.cycleGraph n

end
end SpectraCommonGraphs
