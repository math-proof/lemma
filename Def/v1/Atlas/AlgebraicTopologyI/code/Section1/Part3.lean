/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section1.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.GroupTheory.FreeAbelianGroup
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.Grp.Basic
import Mathlib.Algebra.Category.Grp.Colimits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Category.Grp.Abelian
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section1


namespace AlgebraicTopologyI

open Finset AlgebraicTopology CategoryTheory

/-- **Definition 1.4**. The singular chain complex $S_*(X; \mathbb{Z})$ of a topological
space $X$ with integer coefficients, as a chain complex of abelian groups indexed by
$\mathbb{N}$ with the differential $\partial$ assembled from face maps. -/
noncomputable def singularChainComplexZ (X : TopCat.{0}) : ChainComplex AddCommGrpCat ℕ :=
  ((singularChainComplexFunctor AddCommGrpCat).obj (AddCommGrpCat.of ℤ)).obj X

/-- **Definition 1.7**. The $n$-th singular homology group with integer coefficients,
$H_n(X; \mathbb{Z}) = Z_n(X) / B_n(X)$, packaged as an abelian group. -/
noncomputable def SingularHomologyGroup (n : ℕ) (X : Type) [TopologicalSpace X] :
    AddCommGrpCat :=
  ((singularHomologyFunctor AddCommGrpCat n).obj (AddCommGrpCat.of ℤ)).obj (TopCat.of X)

end AlgebraicTopologyI
