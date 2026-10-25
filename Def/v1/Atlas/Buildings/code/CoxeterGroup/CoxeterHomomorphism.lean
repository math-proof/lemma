/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof
import Mathlib.GroupTheory.Coxeter.Basic
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The geometric representation of $W$: the group homomorphism from $W$ to
$GL(\mathbb{R}^B)$ sending each simple reflection $s_i$ to $\sigma_{s_i}$. -/
noncomputable def coxeterRepresentation (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) :
    W →* ((B → ℝ) ≃ₗ[ℝ] (B → ℝ)) :=
  cs.lift ⟨fun s => sigmaLinearEquiv M s, sigmaLinearEquiv_isLiftable M⟩

end CoxeterGroup
