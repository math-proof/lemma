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
import Def.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs


namespace SpectraCommonGraphs

open Real SimpleGraph Matrix

noncomputable section

open SimpleGraph in
instance boxProd_decidableAdj
    {V W : Type*} [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W) [DecidableRel G.Adj] [DecidableRel H.Adj] :
    DecidableRel (G □ H).Adj := by
  intro ⟨v₁, w₁⟩ ⟨v₂, w₂⟩; rw [SimpleGraph.boxProd_adj]; infer_instance

end
end SpectraCommonGraphs
