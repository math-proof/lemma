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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part4


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
