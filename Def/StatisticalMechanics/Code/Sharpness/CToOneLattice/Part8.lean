/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Theorem.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part3
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable def sctLatticeC (d : ℕ) (β h : ℝ) (n : ℕ) : ℝ :=
  sct_cInfDep (sctBox d) (sctOriginMag d β h) (sctBoxSites d)
    (sctBoxMag d β h) (sctBoxSites_nonempty d) n

end Sharpness
end StatMech
