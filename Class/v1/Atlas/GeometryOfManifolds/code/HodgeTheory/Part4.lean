/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Structure.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part10
set_option autoImplicit false

open DifferentialFormSpace


/-- Typeclass packaging the existence of a Green-operator decomposition for the
Hodge Laplacian. -/
class HasLaplacianGreenDecomp
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (cod : @Codifferential Ω VF inst) where
  green_decomp : Nonempty (@HasGreenOperatorDecomp Ω VF inst (fun α => laplacian cod α))

