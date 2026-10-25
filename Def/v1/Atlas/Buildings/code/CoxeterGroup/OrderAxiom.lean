/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/OrderAxiom.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.SigmaOrder
open CoxeterGroup


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]

set_option linter.unusedSectionVars false

/-- The endomorphism of $\mathbb{R}^B$ associated to a word $s_1 \cdots s_k$,
defined as the product $\sigma_{s_1} \circ \cdots \circ \sigma_{s_k}$ in
$\mathrm{End}_{\mathbb{R}}(\mathbb{R}^B)$. -/
noncomputable def sigmaWord (M : CoxeterMatrix B) : List B → Module.End ℝ (B → ℝ)
  | [] => 1
  | s :: rest => sigmaLin M s * sigmaWord M rest

end CoxeterGroup
