/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part7
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


theorem sctBoxSites_nonempty (d n : ℕ) : (sctBoxSites d n).Nonempty := by
  exact ⟨sctBoxOrigin d n, Finset.mem_univ _⟩


end Sharpness
end StatMech
