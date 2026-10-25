/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/PlanarFKDuality.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.KWGeometricDual.Part22
import Theorem.StatisticalMechanics.Code.BeffaraDC.Duality
open Finset SimpleGraph Set


namespace StatMech

namespace BeffaraDC

open Lattice Ising Walls


noncomputable def pfdClosedDual (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    SimpleGraph (kwg_Face P) where
  Adj C D := C ≠ D ∧ ∃ e : kwg_Edge P,
    e.1 ∉ K.edgeSet ∧ kwg_dualEnds P e = s(C, D)
  symm := by
    constructor
    rintro C D ⟨hne, e, heK, he⟩
    exact ⟨hne.symm, e, heK, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun C h => h.1 rfl⟩

end BeffaraDC
end StatMech
