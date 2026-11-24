module
public import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
public import Def.StatisticalMechanics.Code.FK.PeriodicPlanarCrossingGluing
open Set SimpleGraph Topology


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


@[simp] theorem PeriodicGraph.openSubgraphAmbientHom_apply
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (v : V) :
    P.openSubgraphAmbientHom omega v = v := rfl


end StatMech.FK.PeriodicPlanar
