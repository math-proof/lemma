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
open Finset Set SimpleGraph


namespace StatMech

namespace Lattice

instance instDecidableRelNearestNeighbour (d : ℕ) : DecidableRel (NearestNeighbour d) :=
  fun x y => by unfold NearestNeighbour; infer_instance


instance instDecidableRelAdj (d : ℕ) : DecidableRel (hypercubicLattice d).Adj :=
  instDecidableRelNearestNeighbour d


end Lattice
end StatMech
