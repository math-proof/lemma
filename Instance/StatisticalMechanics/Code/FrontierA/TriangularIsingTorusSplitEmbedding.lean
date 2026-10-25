/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusSplitEmbedding.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusLocalAngularSplit.Part4


namespace StatMech.FrontierA

open SimpleGraph

instance triangularTorusTriple_fact
    (L : Nat) [Fact (2 < L)] : Fact (2 < 3 * L) :=
  ⟨by have := (Fact.out : 2 < L); omega⟩


end StatMech.FrontierA
