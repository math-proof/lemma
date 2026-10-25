/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Def.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Betti-number data for a manifold of dimension `manifoldDim`: total Betti number
$\sum_{i=0}^{\dim M} b_i(M)$ packaged with the cohomology groups. -/
class HasBettiNumbers
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    extends @HasCohomology Ω VF inst where
  manifoldDim : ℕ
  totalBetti : ℕ
  totalBetti_eq : totalBetti = (Finset.range (manifoldDim + 1)).sum
    (fun i => @Module.finrank ℝ (H i) _ (H_addCommGroup i).toAddCommMonoid (H_module i))

