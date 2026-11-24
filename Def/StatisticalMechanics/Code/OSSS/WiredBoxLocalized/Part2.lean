module
public import Theorem.StatisticalMechanics.Code.OSSS.LocalizedCrossTree
public import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxDifferential.Part5
public import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
public import Theorem.StatisticalMechanics.Code.FK.OffCentreSandwichProof.Part6
public import Theorem.StatisticalMechanics.Code.OSSS.WiredDenominatorArithmetic
public import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxLocalized
open scoped BigOperators Classical


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxLocalized.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech

namespace OSSS

namespace WiredBoxLocalized

open Lattice RevealmentConstruction AdaptiveCovLowerGeom

open LocalizedCrossTree WiredBoxDifferential

open FK DecisionTree RevealmentTranslation


noncomputable def innerCrossInd (d n : Nat) :
    ConfigSpace (boxGraph d (2 * n)).edgeSet -> Real := fun omega =>
  crossIndG (boxActiveEdge d n) 0 n
    (restrictConfig (boxActiveEdgeLE d (n_le_two_mul n)) omega)

end WiredBoxLocalized
end OSSS
end StatMech
