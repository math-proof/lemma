/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/DeletionInjectivity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivityHelpers
import Mathlib.GroupTheory.Coxeter.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.DeletionInjectivity
open CoxeterSystemFromDeletion Function Set


namespace CoxeterSystemFromDeletion

variable {B : Type*} {W : Type*} [Group W]

/-- Main theorem: a pair $(W, \mathtt{gen})$ satisfying the deletion condition,
together with generators that are involutions with no length-$2$ relations,
forms a Coxeter system for the canonically associated Coxeter matrix. -/
noncomputable def deletion_implies_coxeter_system
    (gen : B → W) (hgen_inv : ∀ s, gen s * gen s = 1)
    (hgen_ne : ∀ s t, s ≠ t → gen s * gen t ≠ 1)
    (hgen_surj : Subgroup.closure (Set.range gen) = ⊤)
    (hDel : SatisfiesDeletionConditionGen gen) :
    CoxeterSystem (deletionCoxeterMatrix gen hgen_inv hgen_ne) W :=
  let M := deletionCoxeterMatrix gen hgen_inv hgen_ne
  let φ := deletionCanonicalHom gen hgen_inv hgen_ne
  let hφ_surj := deletionCanonicalHom_surjective gen hgen_inv hgen_ne hgen_surj
  let hφ_inj := deletionCanonicalHom_injective gen hgen_inv hgen_ne hgen_surj hDel

  let e : M.Group ≃* W := MulEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩

  ⟨e.symm⟩

end CoxeterSystemFromDeletion
