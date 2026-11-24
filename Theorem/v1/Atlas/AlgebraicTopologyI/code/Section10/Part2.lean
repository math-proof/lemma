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
public import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part4
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

/-- Compatibility: the small-complex factorization of `C_*(A) ↪ C_*(X)` composed with the
inclusion of the small complex into `C_*(X)` recovers the original inclusion. -/
lemma smallChainInclusionA_comp_ι (X : Type) [TopologicalSpace X] (A B : Set X) :
    smallChainInclusionA X A B ≫ smallChainInclusion X A B =
    subspaceChainInclusion X A := by
  change (biprod.inl ≫ factorThruImage
    (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B))) ≫
    image.ι (biprod.desc (subspaceChainInclusion X A) (subspaceChainInclusion X B)) = _
  rw [Category.assoc, image.fac, biprod.inl_desc]

end
end Excision
