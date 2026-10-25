/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/FKSharpnessWeightedLocalized.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedStrict
open scoped BigOperators Classical
open Finset Set


namespace StatMech

namespace OSSS

namespace FKSharpnessWeightedLocalized

open Lattice FK RevealmentConstruction RevealmentTranslation

open AdaptiveCovLowerGeom LocalizedCrossTree DecisionTree

open WiredBoxDifferential WiredBoxLocalized

open ActiveBoundaryDifferential LindebergTree RussoPrefactor

open FKSharpnessWeightedPeriodic FKSharpnessWeightedPeriodicRepair

open FKSharpnessWeightedStrict


noncomputable def weightedLocalizedTheta
    (d n : Nat) (J : Sym2 (Site d) -> Real) (q beta : Real) : Real :=
  Lindeberg.mean
    (activeBCProb (boxGraph d (2 * n))
      (wiredBoxBoundaryGraph d (2 * n))
      (betaParams (boxCoupling J (2 * n)) beta) q)
    (innerCrossInd d n)


end FKSharpnessWeightedLocalized
end OSSS
end StatMech
