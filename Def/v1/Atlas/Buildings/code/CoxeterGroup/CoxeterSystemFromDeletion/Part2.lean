/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion.Part2
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The canonical group homomorphism from the abstract Coxeter group on $B$
(with the matrix induced by the family $\mathtt{gen}$) to $W$, sending each
generator $\mathtt{simple}\,s$ to $\mathtt{gen}\,s$. -/
noncomputable def deletionCanonicalHom
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) :
    (deletionCoxeterMatrix gen hgen_inv hgen_ne).Group →* W :=
  (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.lift
    ⟨gen, deletionCoxeterMatrix_isLiftable gen hgen_inv hgen_ne⟩

end CoxeterSystemFromDeletion
