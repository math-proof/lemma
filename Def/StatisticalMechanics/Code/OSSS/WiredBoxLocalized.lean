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
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open LocalizedCrossTree WiredBoxDifferential

open FK DecisionTree RevealmentTranslation


def boxActiveEdgeLE (d : Nat) {n m : Nat} (h : n <= m) :
    (boxGraph d n).edgeSet -> (boxGraph d m).edgeSet := fun e =>
  ⟨innerEdgeLE d h e.1, by
    have he : e.1 ∈ (boxGraph d n).edgeFinset := by
      rw [SimpleGraph.mem_edgeFinset]
      exact e.2
    have hout := ocs_innerEdgeLE_mem_edgeFinset d h e.1 he
    rwa [SimpleGraph.mem_edgeFinset] at hout⟩

end WiredBoxLocalized
end OSSS
end StatMech
