module
public import Def.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerChainRule
public import Theorem.Finset.Atlas.v1.ProbabilisticMethodsInCombinatorics.code.Chapter10.ShearerChainRule
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Analysis.Convex.Jensen
public import Mathlib.Data.Finset.Image
set_option maxHeartbeats 800000
open Finset BigOperators Real ShannonEntropy


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter10/ShearerCombinatorial.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace ShearerCombinatorial

/-- Projection of `x : Fin n → α` onto all coordinates except the $i$-th one. -/
def coordProject {n : ℕ} {α : Type*} (i : Fin n) (x : Fin n → α) :
    ↥(Finset.univ.erase i : Finset (Fin n)) → α :=
  fun ⟨j, _⟩ => x j

end ShearerCombinatorial
