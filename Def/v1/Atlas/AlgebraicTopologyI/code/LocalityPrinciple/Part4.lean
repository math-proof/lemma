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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part3


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- The restriction of $\mathrm{Sd}^k$ to the subgroup of $\mathcal{A}$-small
chains, as an endomorphism of that subgroup. -/
def smallIterateSubdivision {X : Type*} [TopologicalSpace X]
    (𝒜 : Set (Set X)) (n : ℕ) (k : ℕ) :
    (smallChainSubgroup n 𝒜 : AddSubgroup (SingularChains n X)) →+
    (smallChainSubgroup n 𝒜 : AddSubgroup (SingularChains n X)) :=
  ((iterateSubdivisionHom n k).restrict (smallChainSubgroup n 𝒜)).codRestrict
    (smallChainSubgroup n 𝒜)
    (fun ⟨c, hc⟩ => iterateSubdivision_mem_smallChainSubgroup 𝒜 n k c hc)

/-- The subdivision operator commutes with the boundary on the standard simplex,
verified by transporting to the categorical singular chain complex via
`singularChainsLift` where the corresponding statement is naturality of the
subdivision operator. -/
def stdHomotopyKChain (n : ℕ) (k : ℕ) :
    SingularChains (n + 1) ↥(stdSimplex ℝ (Fin (n + 1))) :=
  Classical.choice ⟨0⟩

/-- The chain homotopy operator $h_k : S_n(X) \to S_{n+1}(X)$ witnessing
$\mathrm{Sd}^k \simeq \mathrm{id}$. It is obtained on each generator $\sigma$ by
pushing forward the universal chain `stdHomotopyKChain` along $\sigma$. -/
def homotopyOpK {X : Type*} [TopologicalSpace X] (n : ℕ) (k : ℕ) :
    SingularChains n X →+ SingularChains (n + 1) X :=
  FreeAbelianGroup.lift fun σ : SingularSimplex n X =>
    (SingularChains.map (show C(↥(stdSimplex ℝ (Fin (n + 1))), X) from σ) :
      SingularChains (n + 1) ↥(stdSimplex ℝ (Fin (n + 1))) →+
      SingularChains (n + 1) X) (stdHomotopyKChain n k)

end LocalityPrinciple
end
