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
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part15
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI


namespace SphereHomology

open AlgebraicTopology

section SuspensionIsoProof

open AlgebraicTopology

noncomputable section

/-- Local copy of `pairSES_f_mono` for the suspension-isomorphism proof. -/
instance suspPairSES_f_mono (X : Type) [TopologicalSpace X] (A : Set X) :
    Mono (suspPairSES X A).f := suspInclChainMono X A

/-- Local copy of `pairSES_g_epi` for the suspension-isomorphism proof. -/
instance suspPairSES_g_epi (X : Type) [TopologicalSpace X] (A : Set X) :
    Epi (suspPairSES X A).g := by
  change Epi (cokernel.π (suspInclChain X A))
  infer_instance

end
end SuspensionIsoProof
end SphereHomology
