/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineSLV.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Lemma.Finset.Any_And_All_Eq.of.IsMaximal.In_Faces.In_Apartments
import Structure.v1.Atlas.Buildings.code.Building.Basic.Part2
import Def.v1.Atlas.Buildings.code.Building.Affine.Part2
import Def.v1.Atlas.Buildings.code.Building.AffineSLV.Part3
set_option linter.unusedSectionVars false


namespace AffineBuildingSLVAxioms

set_option linter.unusedVariables false

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- The identification of the Iwahori subgroup with the stabiliser of the
standard periodic flag: a pair of mutual implications between "upper
triangular mod $\pi$" and "stabilises the flag". -/
structure IwahoriIdentification (pf : AffineBuildingSLV.PeriodicFlag C) where
  stabilizer_implies_upper_tri :
    ∀ g : Fin C.n → Fin C.n → C.𝔬,
      StabilizesStandardFlag C g pf → IsUpperTriangularModM C g
  upper_tri_implies_stabilizer :
    ∀ g : Fin C.n → Fin C.n → C.𝔬,
      IsUpperTriangularModM C g → StabilizesStandardFlag C g pf

end AffineBuildingSLVAxioms
