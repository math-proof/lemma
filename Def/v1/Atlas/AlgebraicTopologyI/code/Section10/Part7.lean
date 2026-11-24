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
public import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part5
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

attribute [instance] subspaceChainInclusion_mono

/-- Forward direction of the abstract second isomorphism: a map from `coker(pullback.snd)`
to `coker(biprod.inl ∘ factorThruImage)`, induced by the inclusion of `ℬ` into the
biproduct. -/
def secondIso_fwd :
    cokernel (pullback.snd (f := φ) (g := ψ)) ⟶
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) :=
  cokernel.desc _ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫
    cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) (secondIso_fwd_cond φ ψ)

/-- Inverse direction of the abstract second isomorphism: the descent of
`secondIso_imgToCokerPS` from the image to `coker(biprod.inl ∘ factorThruImage)`. -/
def secondIso_inv :
    cokernel (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ⟶
    cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (secondIso_imgToCokerPS φ ψ) (secondIso_inv_kills_inclA φ ψ)

end
end Excision
