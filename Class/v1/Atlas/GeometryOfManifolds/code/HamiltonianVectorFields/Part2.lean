/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HamiltonianVectorFields.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Structure.v1.Atlas.GeometryOfManifolds.code.SymplecticManifolds.Part3
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.SymplecticManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HamiltonianVectorFields
set_option autoImplicit false

open DifferentialFormSpace


/-- Interface providing a **Lie bracket** $[X, Y]$ of vector fields characterised by the
identity $\iota_{[X, Y]} \alpha = \mathcal{L}_X (\iota_Y \alpha) - \iota_Y (\mathcal{L}_X \alpha)$
for every form $\alpha$ of positive degree. -/
class HasLieBracket (Ω : ℕ → Type*) (VF : Type*) [inst : DifferentialFormSpace Ω VF] where
  bracket : VF → VF → VF
  bracket_ι_eq : ∀ (X Y : VF) {p : ℕ} (α : Ω (p + 1)),
    inst.ι (bracket X Y) α = inst.L X (inst.ι Y α) - inst.ι Y (inst.L X α)


