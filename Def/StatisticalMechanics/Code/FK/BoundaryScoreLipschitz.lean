/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryScoreLipschitz.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.ComparisonHolley.Part3
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.Tilt.Part3


namespace StatMech.FK

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


def configHammingCount (omega eta : ConfigSpace (Sym2 V)) : Nat :=
  (diffSet G omega eta).card + (diffSet G eta omega).card


end
end StatMech.FK
