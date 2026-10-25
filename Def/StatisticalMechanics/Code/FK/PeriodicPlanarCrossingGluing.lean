/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCrossingGluing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
open Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


def PeriodicGraph.openSubgraphAmbientHom (P : PeriodicGraph V)
    (omega : ConfigSpace (Sym2 V)) : P.openSubgraph omega →g P.graph :=
  SimpleGraph.Hom.ofLE fun _ _ h => h.1

end StatMech.FK.PeriodicPlanar
