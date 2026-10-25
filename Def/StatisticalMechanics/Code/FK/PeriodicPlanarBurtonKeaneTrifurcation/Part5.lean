/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarBurtonKeaneTrifurcation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneMerge.Part3
import Theorem.StatisticalMechanics.Code.FrontierA.FiniteCutHubCount
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarBurtonKeaneTrifurcation.Part4
open Filter MeasureTheory Set SimpleGraph Topology Finset
open scoped ENNReal BigOperators


namespace StatMech.FK.PeriodicPlanar

open Lattice StatMech.FrontierA

variable {V : Type*} [Countable V] [DecidableEq V]


noncomputable def PeriodicGraph.orbitTrifurcationCoords
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) : Finset (Site 2) :=
  by
    classical
    exact (box_finite 2 n).toFinset.filter
      (fun z => P.IsTrifurcation omega (P.shift z u))

noncomputable def PeriodicGraph.orbitTrifurcationHubs
    (P : PeriodicGraph V) (u : V) (omega : ConfigSpace (Sym2 V))
    (n : Nat) : Finset V :=
  (P.orbitTrifurcationCoords u omega n).image (fun z => P.shift z u)

end StatMech.FK.PeriodicPlanar
