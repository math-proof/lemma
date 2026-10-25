/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarGraph.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.Lattice.PlanarTopology.Part4
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarGraph
open Finset Set SimpleGraph
open MeasureTheory


namespace StatMech

namespace FK

namespace PeriodicPlanar

open Lattice


structure PeriodicGraph (V : Type*) [DecidableEq V] where
  graph : SimpleGraph V
  shift : Site 2 → V ≃ V
  shift_zero : shift 0 = Equiv.refl V
  shift_add : ∀ z w v, shift (z + w) v = shift w (shift z v)
  shift_adj : ∀ z x y, graph.Adj (shift z x) (shift z y) ↔ graph.Adj x y
  fundamentalDomain : Finset V
  fundamentalDomain_nonempty : fundamentalDomain.Nonempty
  covers : ∀ v, ∃ z u, u ∈ fundamentalDomain ∧ shift z u = v
  locallyFinite : SimpleGraph.LocallyFinite graph

end PeriodicPlanar
end FK
end StatMech
