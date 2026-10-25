/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/BraidRelationProof/Assembly.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.DihedralHelpers.Part2
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.BraidRelationProof.Assembly
open Finset BigOperators Real


namespace CoxeterGroup

variable {B : Type*} [DecidableEq B] [Fintype B]


/-- The coefficient $\alpha$ in the decomposition $v = \alpha e_s + \beta e_t +
w$ where $w$ is $B$-orthogonal to both $e_s$ and $e_t$. -/
noncomputable def decompAlpha (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : ℝ :=
  (bilinForm M v (e s) - formVal M s t * bilinForm M v (e t)) /
  (1 - formVal M s t ^ 2)

/-- The coefficient $\beta$ in the orthogonal decomposition of $v$ along
$e_s, e_t$, complementary to $\alpha$. -/
noncomputable def decompBeta (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : ℝ :=
  (bilinForm M v (e t) - formVal M s t * bilinForm M v (e s)) /
  (1 - formVal M s t ^ 2)

/-- The orthogonal complement $w = v - \alpha e_s - \beta e_t$ of $v$ in the
$(e_s, e_t)$-plane. -/
noncomputable def decompW (M : CoxeterMatrix B) (s t : B) (v : B → ℝ) : B → ℝ :=
  v - decompAlpha M s t v • e s - decompBeta M s t v • e t

end CoxeterGroup
