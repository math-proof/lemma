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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple


noncomputable section

open CategoryTheory AlgebraicTopologyI Finset BigOperators BarycentricSubdivision

namespace LocalityPrinciple

variable (X : TopCat.{0}) (𝒜 : Set (Set X))

/-- The restriction of the singular boundary map to the subcomplex of
$\mathcal{A}$-small chains, giving the differential of $S_*^{\mathcal{A}}(X)$. -/
def smallBoundaryMap {X : Type*} [TopologicalSpace X] (n : ℕ) (𝒜 : Set (Set X)) :
    (smallChainSubgroup (n + 1) 𝒜 : AddSubgroup (SingularChains (n + 1) X)) →+
    (smallChainSubgroup n 𝒜 : AddSubgroup (SingularChains n X)) :=
  ((boundaryMap n X).restrict (smallChainSubgroup (n + 1) 𝒜)).codRestrict
    (smallChainSubgroup n 𝒜)
    (fun ⟨c, hc⟩ => boundaryMap_mem_smallChainSubgroup 𝒜 c hc)

set_option maxHeartbeats 400000 in

/-- The singular boundary maps satisfy $\partial_n \circ \partial_{n+1} = 0$,
making singular chains into a chain complex. -/
def singularChainsLift (X : TopCat.{0}) (n : ℕ) :
    SingularChains n X →+
      (singularChainComplexZ X).X n :=
  FreeAbelianGroup.lift (fun (σ : SingularSimplex n X) =>
    (Limits.Sigma.ι (fun _ : (TopCat.toSSet.obj X).obj (Opposite.op (SimplexCategory.mk n)) ↦
      AddCommGrpCat.of ℤ) ((TopCat.toSSetObjEquiv X (Opposite.op (SimplexCategory.mk n))).symm σ)) (1 : ℤ))

end LocalityPrinciple
end
