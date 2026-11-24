module
public import Theorem.StatisticalMechanics.Code.Universality.HexFiniteRegion.Part4
public import Theorem.StatisticalMechanics.Code.Universality.HexInfraWinding
public import Theorem.StatisticalMechanics.Code.Universality.HexCyclicVertexPartition.Part5


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexCyclicVertexPartition.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.Universality

open Complex Function HexWalk

open scoped BigOperators

noncomputable section

variable {region : ℂ → Prop} {a : ℂ} {h0 : ℤ} {v du : ℂ}


def hexDecodedTurns (n : ℕ) : List ℤ :=
  (Encodable.decode n : Option (List ℤ)).getD []

end
end StatMech.Universality
