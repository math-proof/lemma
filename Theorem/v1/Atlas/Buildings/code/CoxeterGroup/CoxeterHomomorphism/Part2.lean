/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/CoxeterHomomorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof
import Mathlib.GroupTheory.Coxeter.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.CoxeterHomomorphism
open Finset BigOperators CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The geometric representation sends a simple generator $s_i$ to the
corresponding reflection $\sigma_{s_i}$ as a linear equivalence. -/
@[simp]
theorem coxeterRepresentation_simple (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (s : B) :
    coxeterRepresentation M cs (cs.simple s) = sigmaLinearEquiv M s :=
  cs.lift_apply_simple (sigmaLinearEquiv_isLiftable M) s


/-- The action of $\rho(\mathtt{wordProd}\,\omega)$ on a vector $v$ is exactly
the iterated reflection $\sigma_{s_{i_1}} \cdots \sigma_{s_{i_k}}(v)$
encoded by $\mathtt{wordSigma}$. -/
theorem coxeterRepresentation_wordProd_apply (M : CoxeterMatrix B) {W : Type*} [Group W]
    (cs : CoxeterSystem M W) (word : List B) (v : B → ℝ) :
    (coxeterRepresentation M cs (cs.wordProd word)) v = wordSigma M word v := by
  induction word with
  | nil =>
    simp [CoxeterSystem.wordProd_nil, wordSigma_nil, map_one, LinearEquiv.coe_one]
  | cons s rest ih =>
    rw [CoxeterSystem.wordProd_cons, map_mul]

    show (coxeterRepresentation M cs (cs.simple s) *
          coxeterRepresentation M cs (cs.wordProd rest)) v = _

    simp only [LinearEquiv.mul_apply]
    rw [coxeterRepresentation_simple]

    simp only [sigmaLinearEquiv_apply, ih]

    rfl

end CoxeterGroup
