/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section16.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.FreeAbelianGroup
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section15
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section10
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
import Mathlib.Algebra.Category.Grp.Abelian


namespace CWComplex

variable (X : Type*) [TopologicalSpace X] [Topology.CWComplex (Set.univ : Set X)]

/-- **Definition 16.1.** The group of cellular `n`-chains of a CW complex `X`, defined as the
free abelian group on the set of `n`-cells of `X`. -/
abbrev cellularChains (n : ℕ) : Type _ :=
  FreeAbelianGroup (cells X n)

end CWComplex
