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
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section10.Part4
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

attribute [instance] subspaceChainInclusion_mono

/-- The induced map `coim([φ, ψ]) → coker(pullback.snd)` from the coimage of the biproduct
map to the cokernel of the pullback projection. -/
def secondIso_coimToCokerPS :
    Abelian.coimage (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  cokernel.desc _ (biprod.snd ≫ cokernel.π (pullback.snd (f := φ) (g := ψ)))
    (secondIso_kernel_kills_snd_cokernel φ ψ)

/-- The induced map `image([φ, ψ]) → coker(pullback.snd)`, obtained from
`secondIso_coimToCokerPS` via the canonical iso `image ≅ coimage` in an abelian category. -/
def secondIso_imgToCokerPS :
    Limits.image (biprod.desc φ ψ) ⟶ cokernel (pullback.snd (f := φ) (g := ψ)) :=
  (Abelian.coimageIsoImage' (biprod.desc φ ψ)).inv ≫ secondIso_coimToCokerPS φ ψ

end
end Excision
