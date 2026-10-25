/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/MinCut/ContractionAlgorithm.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib


noncomputable section

open Finset

namespace MinCut

structure Multigraph (V : Type*) [Fintype V] [DecidableEq V] where
  edgeMult : V → V → ℕ
  symm : ∀ u v, edgeMult u v = edgeMult v u
  no_loops : ∀ v, edgeMult v v = 0

end MinCut
end
