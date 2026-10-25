/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/CToOneLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Sharpness.CToOne.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeDomain
import Def.StatisticalMechanics.Code.Sharpness.CToOneLattice.Part2
open Filter Topology


namespace StatMech

namespace Sharpness

open Ising Lattice


noncomputable instance sctBoxInLargerDecidable (d n m : ℕ) :
    DecidablePred (sctBoxInLarger d n m) := Classical.decPred _


end Sharpness
end StatMech
