/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldArrayClosure.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldMacroArrayAssembly.Part2
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldArrayClosure.Part4
open Filter MeasureTheory Set Topology


namespace StatMech.FK.PeriodicPlanar

open Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}

noncomputable def PeriodicPlaneEmbedding.connectorMarginRequirement
    (E : PeriodicPlaneEmbedding P) (radius : Nat) : Nat :=
  Nat.ceil (max
    (E.orbitBoxCoordinateBound (P.bufferedRadius radius) 0)
    (E.orbitBoxCoordinateBound (P.bufferedRadius radius) 1))

end StatMech.FK.PeriodicPlanar
