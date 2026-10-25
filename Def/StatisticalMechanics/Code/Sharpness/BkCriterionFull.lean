/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BkCriterionFull.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterion.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BkCriterionFull
open MeasureTheory Finset
open scoped NNReal


namespace StatMech

namespace Sharpness

open ConfigSpace SimpleGraph

variable {V : Type*}


def shk_boundaryPairs [Fintype V] [DecidableEq V] (G : SimpleGraph V) (S : Finset V)
    [DecidableRel G.Adj] : Finset (V × V) :=
  Finset.univ.filter (fun q => q.1 ∈ S ∧ q.2 ∉ S ∧ G.Adj q.1 q.2)

end Sharpness
end StatMech
