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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part6
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace Excision

open AlgebraicTopology Set

noncomputable section

attribute [instance] subspaceChainInclusion_mono

/-- Vanishing condition needed to descend `secondIso_imgToCokerPS` to a map out of the
cokernel `coker(biprod.inl ∘ factorThruImage)`. -/
lemma secondIso_inv_kills_inclA :
    (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ≫ secondIso_imgToCokerPS φ ψ = 0 := by
  simp only [secondIso_imgToCokerPS, secondIso_coimToCokerPS, Category.assoc,
    ← Category.assoc (factorThruImage _), Abelian.factorThruImage_comp_coimageIsoImage'_inv,
    cokernel.π_desc, biprod.inl_snd_assoc, zero_comp]

end
end Excision
