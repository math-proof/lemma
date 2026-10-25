/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.AlgebraicTopologyI.code.ModelChains
import Structure.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence
open Finset BigOperators


namespace AlgebraicTopologyI

noncomputable section

open ContinuousMap

/-- The bottom inclusion `X → X × I` given by `x ↦ (x, 0)`. -/
noncomputable def inclusion0 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨0, unitInterval.zero_mem⟩)

/-- The top inclusion `X → X × I` given by `x ↦ (x, 1)`. -/
noncomputable def inclusion1 (X : Type) [TopologicalSpace X] :
    C(X, X × ↥I) :=
  ContinuousMap.prodMk (ContinuousMap.id X) (ContinuousMap.const X ⟨1, unitInterval.one_mem⟩)

end
end AlgebraicTopologyI
