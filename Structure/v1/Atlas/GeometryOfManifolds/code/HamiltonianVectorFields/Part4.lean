/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields.Part2
set_option autoImplicit false

open DifferentialFormSpace


/-- **Flux data** of a symplectic isotopy $\varphi_t$: a closed 1-form $\sigma$ representing the
class $[\iota_{X_t}\omega] \in H^1(M; \mathbb{R})$ uniformly in $t$, i.e. each
$\sigma - \iota_{X_t}\omega$ is exact. The flux of $\varphi$ is the cohomology class
$[\sigma]$. -/
structure FluxData
    {Ω : ℕ → Type*} {VF : Type*}
    [inst : DifferentialFormSpace Ω VF]
    (S : SymplecticManifold Ω VF)
    (iso : SymplecticIsotopy S) where
  representative : Ω 1
  is_closed : inst.d representative = 0
  cohomologous_to_ιXω : ∀ t, IsExact' VF (representative - inst.ι (iso.X_t t) S.ω)


