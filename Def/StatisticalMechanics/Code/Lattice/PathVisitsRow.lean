/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/PathVisitsRow.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.PathVisitsRow
open Set Finset SimpleGraph


namespace StatMech

namespace Lattice

noncomputable def pvr_firstIdxAtCoord {a b : Site 2} (w : (hypercubicLattice 2).Walk a b)
    (k : Fin 2) (r : ℤ) (h : ∃ i, (w.getVert i) k = r) : ℕ :=
  Nat.find h


end Lattice
end StatMech
