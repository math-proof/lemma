/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineIsometryAxiomsAction.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AffineIsometry
import sympy.atlas.v1.Atlas.Buildings.code.Building.GroupApplicationsCh17
import Lemma.Set.ConjSet.eq.Image

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open AffineIsometryBuilding DVRContext

/-- An $n \times n$ matrix over $\mathfrak{o}$ is upper-triangular modulo
$\mathfrak{m}$ if every strictly-below-diagonal entry is divisible by the
uniformizer $\pi$. -/
def IsUpperTriangularModM_Isometry (C : DVRContext)
    (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, i.val > j.val →
    ∃ h : C.𝔬, g i j = C.uniformizer * h

/-- A matrix is congruent to the identity modulo $\mathfrak{m}$ if each entry
differs from the corresponding entry of the identity matrix by a multiple of
the uniformizer $\pi$. -/
def IsCongruentToIdentity_Isometry (C : DVRContext)
    (g : Fin C.n → Fin C.n → C.𝔬) : Prop :=
  ∀ i j : Fin C.n, ∃ h : C.𝔬,
    g i j - (if i = j then 1 else 0) = C.uniformizer * h

/-- The Iwahori subgroup of the isometry group in the alternating-form setting:
matrices that are upper-triangular modulo $\mathfrak{m}$. -/
def IwahoriSubgroup_Alternating (C : DVRContext) :
    Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | IsUpperTriangularModM_Isometry C g}

namespace Isometry

/-- The parahoric subgroup associated to a lattice chain and an index set
$J$: matrices preserving each $\mathfrak{o}$-lattice $\Lambda_j$ for
$j \in J$. -/
def ParahoricSubgroup (C : DVRContext)
    (chain : ℤ → OLattice C) (J : Set ℤ) :
    Set (Fin C.n → Fin C.n → C.𝔬) :=
  {g | ∀ j ∈ J, ∀ v ∈ (chain j).carrier,
    (fun k => ∑ l, C.embed (g k l) * v l) ∈ (chain j).carrier}

end Isometry
