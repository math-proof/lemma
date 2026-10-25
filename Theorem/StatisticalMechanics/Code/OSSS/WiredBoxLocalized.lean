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
import Def.StatisticalMechanics.Code.OSSS.WiredBoxLocalized
open scoped BigOperators Classical


namespace StatMech

namespace OSSS

namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open LocalizedCrossTree WiredBoxDifferential

open FK DecisionTree RevealmentTranslation


theorem boxActiveEdgeLE_injective (d : Nat) {n m : Nat} (h : n <= m) :
    Function.Injective (boxActiveEdgeLE d h) := by
  intro e f hef
  apply Subtype.ext
  have hv := congrArg Subtype.val hef
  change innerEdgeLE d h e.1 = innerEdgeLE d h f.1 at hv
  have hvinj : Function.Injective (boxVertInclLE d h) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : boxVerts d m => (z : Site d)) hxy
  exact (Sym2.map.injective hvinj) hv

theorem n_le_two_mul (n : Nat) : n <= 2 * n := by omega


end WiredBoxLocalized
end OSSS
end StatMech
