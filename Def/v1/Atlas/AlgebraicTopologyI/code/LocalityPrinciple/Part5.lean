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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part4


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

/-- The restriction of the homotopy operator $h_k$ to the subgroup of
$\mathcal{A}$-small chains. -/
def smallHomotopyOpK {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (n : ℕ) (k : ℕ) :
    (smallChainSubgroup n 𝒜 : AddSubgroup (SingularChains n X)) →+
    (smallChainSubgroup (n + 1) 𝒜 : AddSubgroup (SingularChains (n + 1) X)) :=
  ((homotopyOpK n k).restrict (smallChainSubgroup n 𝒜)).codRestrict
    (smallChainSubgroup (n + 1) 𝒜)
    (fun ⟨c, hc⟩ => homotopyOpK_mem_smallChainSubgroup 𝒜 n k c hc)

end LocalityPrinciple
end
