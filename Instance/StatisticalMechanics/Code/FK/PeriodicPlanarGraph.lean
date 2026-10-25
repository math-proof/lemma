/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Abbrev.StatisticalMechanics.Code.FK.PeriodicPlanarGraph
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable instance PeriodicGraph.instFintypeOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : Fintype (P.OrbitVertex n) :=
  Fintype.ofFinset (P.orbitBox n) (fun _ => Iff.rfl)

instance PeriodicGraph.instDecidableEqOrbitVertex
    (P : PeriodicGraph V) (n : ℕ) : DecidableEq (P.OrbitVertex n) :=
  Subtype.instDecidableEq


end PeriodicPlanar
end FK
end StatMech
