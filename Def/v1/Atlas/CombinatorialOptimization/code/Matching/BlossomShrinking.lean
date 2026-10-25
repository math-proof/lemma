/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/CombinatorialOptimization/code/Matching/BlossomShrinking.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.CombinatorialOptimization.code.Matching.Berge
import Lemma.Finset.Atlas.v1.CombinatorialOptimization.code.Matching.Berge
open SimpleGraph


namespace SimpleGraph

variable {V : Type*} [DecidableEq V] [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def blossomContractMap (B : Finset V) (base : V) : V → V :=
  fun v => if v ∈ B then base else v

def contractBlossom (G : SimpleGraph V) (B : Finset V) (base : V) : SimpleGraph V :=
  G.map (blossomContractMap B base)

end SimpleGraph
