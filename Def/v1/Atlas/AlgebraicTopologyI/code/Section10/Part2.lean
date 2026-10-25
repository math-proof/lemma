/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
import Abbrev.v1.Atlas.AlgebraicTopologyI.code.Section10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology

noncomputable section

/-- The continuous inclusion `A ↪ X` of a subspace, as a morphism in `TopCat`. -/
def subspaceTopInclusion {X : Type} [TopologicalSpace X] (A : Set X) :
    TopCat.of A ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The chain map `C_*(A; ℤ) → C_*(X; ℤ)` induced by the subspace inclusion `A ↪ X`. -/
def subspaceChainInclusion (X : Type) [TopologicalSpace X] (A : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ singularChainZ.obj (TopCat.of X) :=
  singularChainZ.map (subspaceTopInclusion A)

/-- The *relative singular chain complex* `C_*(X, A; ℤ) := C_*(X) / C_*(A)`, defined as the
cokernel of the chain inclusion `C_*(A) ↪ C_*(X)`. -/
def relativeSingularChainComplex (X : Type) [TopologicalSpace X] (A : Set X) :
    ChainComplex AddCommGrpCat ℕ :=
  cokernel (subspaceChainInclusion X A)

/-- The `n`-th *relative singular homology group* `H_n(X, A; ℤ)`, defined as the `n`-th
homology of the relative singular chain complex `C_*(X, A)`. -/
def RelativeSingularHomologyGroup (n : ℕ) (X : Type) [TopologicalSpace X] (A : Set X) :
    AddCommGrpCat :=
  (HomologicalComplex.homologyFunctor AddCommGrpCat (ComplexShape.down ℕ) n).obj
    (relativeSingularChainComplex X A)

variable (X : Type) [TopologicalSpace X] (A U : Set X)

/-- The continuous inclusion `A ∖ U ↪ A` obtained by viewing `A \ U` first as a subset of
`X \ U` and then forgetting the complement. -/
def excisedSubsetToSubspace :
    TopCat.of (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ⟶ TopCat.of A :=
  TopCat.ofHom ⟨fun ⟨⟨x, _⟩, hx⟩ => ⟨x, hx⟩, by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp continuous_subtype_val⟩

/-- The continuous inclusion `X ∖ U ↪ X`. -/
def complementInclusion :
    TopCat.of (Uᶜ : Set X) ⟶ TopCat.of X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

end
end Excision
