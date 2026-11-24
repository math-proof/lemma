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
public import Instance.v1.Atlas.AlgebraicTopologyI.code.Section10.Part9
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean -/
/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
namespace SphereHomology

open AlgebraicTopology

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section

/-- Local copy of `pairSES` for the suspension-isomorphism proof. -/
def suspPairSES (X : Type) [TopologicalSpace X] (A : Set X) :
    ShortComplex (ChainComplex AddCommGrpCat ℕ) :=
  ShortComplex.mk (suspInclChain X A) (cokernel.π (suspInclChain X A)) (cokernel.condition _)

end
end SuspensionIsoProof
end SphereHomology
