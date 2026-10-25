/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.SubdivisionSmall
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section13
import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Homology.Homotopy
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.Ab
import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part2


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- At each degree, the inclusion $S_n^{\mathcal{A}}(X) \hookrightarrow S_n(X)$ is
injective: it factors as the subgroup inclusion followed by the injective lift. -/
def iterateSubdivisionHom {X : Type*} [TopologicalSpace X] (n : ℕ) (k : ℕ) :
    SingularChains n X →+ SingularChains n X :=
  AddMonoidHom.mk' (fun c => iterateSubdivision k c) (iterateSubdivision_add k)

end LocalityPrinciple
end
