/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Valuation/MaximalLattice.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Class.v1.Atlas.Buildings.code.Valuation.LatticesValuations
import Lemma.Nat.IsInO
import Structure.v1.Atlas.Buildings.code.Valuation.MaximalLattice


namespace DVRContext

variable (C : DVRContext)


namespace AnisotropicQuadSpace

variable {C} (B : AnisotropicQuadSpace C)


/-- *The maximal $\mathfrak{o}$-integral set*: vectors $v \in V$ such that $B(v, v) \in
\mathfrak{o}$. This is shown below to be the carrier of the unique maximal
$\mathfrak{o}$-valued lattice. -/
def integralCarrier : Set (Fin C.n → C.k) :=
  { v | C.isInO (B.form v v) }

/-- *$\mathfrak{o}$-valued lattice*: a lattice $\Lambda$ is $\mathfrak{o}$-valued if the form
$B$ takes values in $\mathfrak{o}$ on $\Lambda \times \Lambda$. -/
def IsOValued (Λ : C.OLattice) : Prop :=
  ∀ v w, v ∈ Λ.carrier → w ∈ Λ.carrier → C.isInO (B.form v w)

end AnisotropicQuadSpace
end DVRContext
