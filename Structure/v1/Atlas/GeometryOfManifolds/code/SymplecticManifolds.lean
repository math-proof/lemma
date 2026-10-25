/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/SymplecticManifolds.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.DifferentialForms.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.DifferentialForms
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticLinearAlgebra
import Def.v1.Atlas.GeometryOfManifolds.code.SymplecticLinearAlgebra.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- A **symplectic manifold** (Definition 7): a $2$-form $\omega \in \Omega^2(M)$ that is closed
($d\omega = 0$) and non-degenerate (the contraction map $X \mapsto \iota_X \omega$ is injective). -/
structure SymplecticManifold (Ω : ℕ → Type*) (VF : Type*)
    [inst : DifferentialFormSpace Ω VF] where
  ω : Ω 2
  closed : inst.d ω = 0
  nondegenerate : Function.Injective (fun (X : VF) => inst.ι X ω)


