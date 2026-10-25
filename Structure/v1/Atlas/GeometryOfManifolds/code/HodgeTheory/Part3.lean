/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/GeometryOfManifolds/code/HodgeTheory.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.GeometryOfManifolds.code.KahlerManifolds.Part2
import Lemma.Real.Atlas.v1.GeometryOfManifolds.code.KahlerManifolds
import Def.v1.Atlas.GeometryOfManifolds.code.HodgeTheory.Part3
set_option autoImplicit false

open DifferentialFormSpace


/-- Auxiliary data packaging the formal adjoints $\partial^*$ and $\bar\partial^*$ together
with the decomposition $d^* = \partial^* + \bar\partial^*$. -/
structure DolbeaultLaplacian
    {Ω : ℕ → Type*} {VF : Type*} [inst : DifferentialFormSpace Ω VF]
    (dol : DolbeaultOps (inst := inst))
    (cod : Codifferential (inst := inst)) where
  del_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  delbar_star : ∀ {p : ℕ}, Ω (p + 1) → Ω p
  dstar_decomp : ∀ {p : ℕ} (ω : Ω (p + 1)),
    cod.dstar ω = del_star ω + delbar_star ω
  delbar_star_add : ∀ {p : ℕ} (α β : Ω (p + 1)),
    delbar_star (α + β) = delbar_star α + delbar_star β
  delbar_star_smul : ∀ {p : ℕ} (r : ℝ) (α : Ω (p + 1)),
    delbar_star (r • α) = r • delbar_star α

