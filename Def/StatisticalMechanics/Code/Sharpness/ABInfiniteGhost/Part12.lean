/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABInfiniteGhost.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Probability.InhomogeneousProduct.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.ABGhostRegularity.Part7
import Theorem.StatisticalMechanics.Code.Sharpness.ABThermodynamicPassage
import Theorem.StatisticalMechanics.Code.Sharpness.ABInfiniteGhost.Part11
open Filter MeasureTheory Set SimpleGraph Topology
open scoped NNReal ENNReal


namespace StatMech

namespace Sharpness

open ConfigSpace RandomCurrent

variable {V : Type*}


variable {W : Type*}


def abigUniformFiniteRowBound (G : SimpleGraph V) [DecidableRel G.Adj]
    (J : Sym2 V -> Real) (J0 : Real) : Prop :=
  forall (S : Finset V) (x : S),
    (∑ y : S, if G.Adj (x : V) (y : V)
      then J s((x : V), (y : V)) else 0) <= J0


end Sharpness
end StatMech
