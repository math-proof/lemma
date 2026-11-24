module
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.SubdivisionSmall.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.SubdivisionSmall
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section6
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section13
public import Structure.v1.Atlas.AlgebraicTopologyI.code.Section6
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section13.Part3
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part2


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/LocalityPrinciple.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
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
