/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
import Def.StatisticalMechanics.Code.BeffaraDC.PlanarFKDuality
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


@[simp] theorem pfdClosedDual_adj (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    (C D : kwg_Face P) :
    (pfdClosedDual P K).Adj C D ↔ C ≠ D ∧ ∃ e : kwg_Edge P,
      e.1 ∉ K.edgeSet ∧ kwg_dualEnds P e = s(C, D) :=
  Iff.rfl


end BeffaraDC
end StatMech
