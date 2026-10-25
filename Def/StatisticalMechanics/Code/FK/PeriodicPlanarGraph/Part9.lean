/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph.Part6
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


variable {V : Type*} [DecidableEq V]


noncomputable def square : PeriodicGraph (Site 2) where
  graph := hypercubicLattice 2
  shift := siteTranslate
  shift_zero := siteTranslate_zero
  shift_add := siteTranslate_add
  shift_adj := square_shift_adj
  fundamentalDomain := {0}
  fundamentalDomain_nonempty := ⟨0, by simp⟩
  covers v := ⟨v, 0, by simp, by ext i; simp⟩
  locallyFinite := Lattice.instLocallyFinite 2


def triangularStep (i : Fin 3) : Site 2 :=
  ![![1, 0], ![0, 1], ![-1, 1]] i

end PeriodicPlanar
end FK
end StatMech
