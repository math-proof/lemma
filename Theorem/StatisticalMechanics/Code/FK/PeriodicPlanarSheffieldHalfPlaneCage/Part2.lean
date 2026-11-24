module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrossingFromArms
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldCrosscut
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCluster.Part8
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneJoinedArmsHighProbability.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneTranslation.Part2
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldRotated
public import Mathlib.Topology.Subpath
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlaneCage
open Filter MeasureTheory Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlaneCage.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

namespace ContinuousHalfPlaneCrosscut

@[simp] theorem affinePath_apply (x y : Fin 2 → Real) (t : unitInterval)
    (i : Fin 2) :
    affinePath x y t i = (1 - (t : Real)) * x i + (t : Real) * y i := rfl


end ContinuousHalfPlaneCrosscut
end StatMech.FK.PeriodicPlanar
