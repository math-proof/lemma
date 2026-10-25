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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1


namespace AlgebraicTopologyI

open Finset AlgebraicTopology CategoryTheory

/-- The abelian group structure on $S_n(X)$, inherited from the free abelian group
construction. -/
instance (n : ℕ) (X : Type*) [TopologicalSpace X] : AddCommGroup (SingularChains n X) :=
  inferInstanceAs (AddCommGroup (FreeAbelianGroup (SingularSimplex n X)))

end AlgebraicTopologyI
