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
import Abbrev.v1.Atlas.EllipticCurves.code.FermatsLastTheorem


noncomputable section GaloisRepInfra

open Matrix CongruenceSubgroup

/-- A specific element of the absolute Galois group of `ℚ` realizing complex
conjugation on `Qbar ⊆ ℂ`. -/
def GaloisRepMod.IsIrreducible {ℓ : ℕ} (ρ : GaloisRepMod ℓ) : Prop :=
  ∀ (v : Fin 2 → ZMod ℓ), v ≠ 0 →
    ¬∀ (g : AbsGaloisGroupQ),
      ∃ (c : ZMod ℓ), (↑(ρ g) : Matrix (Fin 2) (Fin 2) (ZMod ℓ)) *ᵥ v = c • v

end GaloisRepInfra
