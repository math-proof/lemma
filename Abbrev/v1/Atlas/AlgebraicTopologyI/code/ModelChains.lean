/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ModelChains.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity.Part2
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.ConvexAcyclicity
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3


namespace AlgebraicTopologyI

noncomputable section

open scoped Topology

/-- The model space for the Eilenberg–Zilber construction in bidegree $(p,q)$: the
product $\Delta^p \times \Delta^q$ of two standard simplices, which serves as the
universal example used in acyclic models. -/
abbrev StdSimplexProd (p q : ℕ) : Type :=
  ↥(stdSimplex ℝ (Fin (p + 1))) × ↥(stdSimplex ℝ (Fin (q + 1)))

end
end AlgebraicTopologyI
