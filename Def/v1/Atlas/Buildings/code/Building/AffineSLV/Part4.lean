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
import Structure.v1.Atlas.Buildings.code.Building.AffineSLV.Part3
set_option linter.unusedSectionVars false


namespace AffineBuildingSLVAxioms

set_option linter.unusedVariables false

variable (C : DVRContext)

attribute [local instance] DVRContext.inst_field DVRContext.inst_comm_ring DVRContext.inst_domain


/-- The Iwahori subgroup as a subset of $M_n(\mathfrak{o})$: matrices that are
upper triangular modulo $\mathfrak{m}$. -/
def IwahoriSubgroup : Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | IsUpperTriangularModM C g}

/-- The carrier of the $i$-th standard lattice in the standard periodic flag,
parametrising vectors whose first $i$ coordinates are in $\pi^{-1}
\mathfrak{o}$ and the remaining ones in $\mathfrak{o}$. -/
def StandardLatticeCarrier (i : Fin C.n) : Set (Fin C.n → C.k) :=
  {v | ∀ j : Fin C.n,
    if j.val < i.val then C.isInO (C.embed C.uniformizer * v j)
    else C.isInO (v j)}

end AffineBuildingSLVAxioms
