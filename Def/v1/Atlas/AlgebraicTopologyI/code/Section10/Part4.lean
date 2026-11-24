module
public import Mathlib
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section5
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
public import Theorem.Set.Atlas.v1.AlgebraicTopologyI.code.LocalityPrinciple
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section5.Part6
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
public import Def.v1.Atlas.AlgebraicTopologyI.code.LocalityPrinciple.Part5
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace Excision

open AlgebraicTopology Set

noncomputable section

/-- The canonical strong epimorphism `C_*(A) ⊕ C_*(B) ↠ C^{\{A, B\}}_*(X)` from the
biproduct to the small singular chain complex for the two-element cover `{A, B}`. -/
def smallChainInclusionA (X : Type) [TopologicalSpace X] (A B : Set X) :
    singularChainZ.obj (TopCat.of A) ⟶ smallChainComplex X A B :=
  biprod.inl ≫ factorThruImage (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))

end
end Excision
