/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PlanarTopology.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PlanarDual.Part10
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part2
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

instance instDecidableRelDualAdj : DecidableRel dualLattice.Adj :=
  instDecidableRelAdj 2


instance instLocallyFiniteDual : SimpleGraph.LocallyFinite dualLattice :=
  instLocallyFinite 2


end Lattice
end StatMech
