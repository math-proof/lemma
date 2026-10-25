/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Structure.StatisticalMechanics.Code.FK.PeriodicPlanarGraph
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def PeriodicGraph.orbitBox (P : PeriodicGraph V) (n : ℕ) : Finset V :=
  (((box_finite 2 n).toFinset ×ˢ P.fundamentalDomain)).image
    (fun zu => P.shift zu.1 zu.2)

end PeriodicPlanar
end FK
end StatMech
