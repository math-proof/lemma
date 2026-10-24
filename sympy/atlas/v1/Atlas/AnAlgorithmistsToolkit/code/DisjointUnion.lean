/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/DisjointUnion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.GraphMatrices
import Lemma.Nat.Atlas.v1.AnAlgorithmistsToolkit.code.GraphMatrices
import Mathlib.Combinatorics.SimpleGraph.Sum
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

namespace DisjointUnion

open Matrix SimpleGraph Finset

section DisjointUnionGraph

variable {V₁ V₂ : Type*} [Fintype V₁] [Fintype V₂] [DecidableEq V₁] [DecidableEq V₂]
variable (G : SimpleGraph V₁) (H : SimpleGraph V₂) [DecidableRel G.Adj] [DecidableRel H.Adj]


instance instDecidableRelSumAdj : DecidableRel (G ⊕g H).Adj := by
  intro a b
  cases a <;> cases b <;> simp [SimpleGraph.sum] <;> infer_instance
