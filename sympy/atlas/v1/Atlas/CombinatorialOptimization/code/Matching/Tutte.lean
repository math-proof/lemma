/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/Tutte.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib

open SimpleGraph

namespace SimpleGraph

variable {V : Type*} [Finite V] {G : SimpleGraph V}

noncomputable def oddComponentCount (G : SimpleGraph V) (X : Set V) : ℕ :=
  ((⊤ : G.Subgraph).deleteVerts X).coe.oddComponents.ncard
