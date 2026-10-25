/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/GeneralInteractionCurrentLimits.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.BoundaryCurrentTail.Part2
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentFiniteMarginals
import Theorem.StatisticalMechanics.Code.FrontierB.InfiniteCurrentCompactness
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FrontierB.GeneralInteractionCurrentLimits
open Filter MeasureTheory Set Topology
open scoped ENNReal


namespace StatMech.FrontierB

open Sharpness Lattice


structure SummableFerromagneticInteraction (d : Nat) where
  coupling : Sym2 (Site d) -> Real
  nonneg : forall e, 0 <= coupling e
  diagonal : forall x, coupling s(x, x) = 0
  translation_invariant : forall (a x y : Site d),
    coupling s(a + x, a + y) = coupling s(x, y)
  summable_origin : Summable (fun y => coupling s((0 : Site d), y))
  irreducible : (positiveInteractionGraph coupling diagonal).Connected


end StatMech.FrontierB
