/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/FermatsLastTheorem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Def.v1.Atlas.EllipticCurves.code.Isogenies.Part13
import Lemma.Complex.Atlas.v1.EllipticCurves.code.Isogenies


noncomputable section GaloisRepInfra

open Matrix CongruenceSubgroup

/-- The algebraic closure of `ℚ` inside `ℂ`, viewed as an intermediate field. This
provides a concrete model of `ℚ̄` sitting inside `ℂ`. -/
abbrev Qbar : IntermediateField ℚ ℂ := algebraicClosure ℚ ℂ

/-- The absolute Galois group of `ℚ`, realized as the group of `ℚ`-algebra
automorphisms of `Qbar`. -/
abbrev AbsGaloisGroupQ := ↥Qbar ≃ₐ[ℚ] ↥Qbar

/-- A mod-`ℓ` Galois representation is a group homomorphism from the absolute Galois
group of `ℚ` to `GL₂(ℤ/ℓℤ)`. -/
abbrev GaloisRepMod (ℓ : ℕ) := AbsGaloisGroupQ →* GL (Fin 2) (ZMod ℓ)

end GaloisRepInfra
