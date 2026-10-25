/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.LocalizedCrossTree
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
import Def.StatisticalMechanics.Code.OSSS.WiredBoxLocalized.Part2
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open LocalizedCrossTree WiredBoxDifferential

open FK DecisionTree RevealmentTranslation


theorem innerCrossInd_monotone (d n : Nat) : Monotone (innerCrossInd d n) := by
  intro omega eta hle
  apply (connectedToSet_increasing (boxActiveEdge d n) 0
    (vertexBoundary d n)).indicator_monotone
  intro e
  exact hle (boxActiveEdgeLE d (n_le_two_mul n) e)

theorem innerCrossInd_idem (d n : Nat)
    (omega : ConfigSpace (boxGraph d (2 * n)).edgeSet) :
    innerCrossInd d n omega * innerCrossInd d n omega = innerCrossInd d n omega := by
  unfold innerCrossInd crossIndG
  rw [Set.indicator_apply]
  split_ifs <;> norm_num


end WiredBoxLocalized
end OSSS
end StatMech
