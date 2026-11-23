/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/ModelChains.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicTopologyI.code.ConvexAcyclicity.Part2
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.ConvexAcyclicity
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section8
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3
public import Def.v1.Atlas.AlgebraicTopologyI.code.ModelChains


namespace AlgebraicTopologyI

public noncomputable section

open scoped Topology

/-- A bidegree-graded family of model chains: a choice, for each pair $(p,q)$, of a
singular $(p+q)$-chain on the product $\Delta^p \times \Delta^q$. This packages the data
of a candidate Eilenberg–Zilber cross product at the level of model spaces. -/
structure ModelChainSystem where
  chains : (p q : ℕ) → SingularChains (p + q) (StdSimplexProd p q)

end
end AlgebraicTopologyI
