/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterSystemFromDeletion.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.OrderOfElement
import Def.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterSystemFromDeletion.Part2
open Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- The canonical homomorphism sends the abstract simple generator
$\mathtt{simple}\,s$ to the concrete involution $\mathtt{gen}\,s$. -/
theorem deletionCanonicalHom_apply_simple
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1) (s : B) :
    deletionCanonicalHom gen hgen_inv hgen_ne
      ((deletionCoxeterMatrix gen hgen_inv hgen_ne).simple s) = gen s :=
  (deletionCoxeterMatrix gen hgen_inv hgen_ne).toCoxeterSystem.lift_apply_simple
    (deletionCoxeterMatrix_isLiftable gen hgen_inv hgen_ne) s

/-- If the image of $\mathtt{gen}$ generates $W$, then the canonical
homomorphism from the abstract Coxeter group to $W$ is surjective. -/
theorem deletionCanonicalHom_surjective
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤) :
    Function.Surjective (deletionCanonicalHom gen hgen_inv hgen_ne) := by
  rw [← MonoidHom.range_eq_top]
  rw [eq_top_iff, ← hgen_surj, Subgroup.closure_le]
  intro w hw
  obtain ⟨s, rfl⟩ := hw
  exact ⟨(deletionCoxeterMatrix gen hgen_inv hgen_ne).simple s,
    deletionCanonicalHom_apply_simple gen hgen_inv hgen_ne s⟩

end CoxeterSystemFromDeletion
