/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Structure.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- The graded and total ranks $\dim HF^i$ and $\sum_i \dim HF^i$ of Floer homology. -/
class HasFloerHomologyRank
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (f : HamiltonianDiffeomorphism S)
    [hnd : IsNondegenerate S f] where
  floerRank : ℕ → ℕ
  totalFloerRank : ℕ


