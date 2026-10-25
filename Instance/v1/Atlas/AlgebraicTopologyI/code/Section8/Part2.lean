/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section8.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.Exact
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.GroupTheory.QuotientGroup.Basic
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section8.Part3


namespace AlgebraicTopologyI

open AlgebraicTopologyI

/-- The relative chain group `S_n(X, A)` inherits an abelian group structure from the
quotient. -/
instance RelativeSingularChains.instAddCommGroup
    (n : ℕ) (X : Type*) [TopologicalSpace X] (A : Set X) :
    AddCommGroup (RelativeSingularChains n X A) :=
  inferInstanceAs (AddCommGroup (SingularChains n X ⧸ (singularChainsInclusion n X A).range))

end AlgebraicTopologyI
