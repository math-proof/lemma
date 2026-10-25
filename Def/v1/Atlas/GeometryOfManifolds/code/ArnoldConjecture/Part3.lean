/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/ArnoldConjecture.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.HamiltonianVectorFields
import Class.v1.Atlas.GeometryOfManifolds.code.ArnoldConjecture.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- Vanishing of Betti numbers above the manifold dimension: $b_i(M) = 0$ for $i > \dim M$. -/
noncomputable def HasBettiNumbers.betti
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (hB : @HasBettiNumbers Ω VF inst) (i : ℕ) : ℕ :=
  @Module.finrank ℝ (hB.H i) _ (hB.H_addCommGroup i).toAddCommMonoid (hB.H_module i)


