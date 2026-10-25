/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Cor1816.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.NumberTheoryI.code.DirichletCharacters
import Lemma.Nat.Atlas.v1.NumberTheoryI.code.DirichletCharacters
import Structure.v1.Atlas.NumberTheoryI.code.Cor1816
open DirichletCharacter


namespace PrimCharDvd

variable {R : Type*} [CommMonoidWithZero R] {m : ℕ}

theorem ext' {p q : PrimCharDvd R m} (hd : p.d = q.d)
    (hχ : hd ▸ p.χ = q.χ) : p = q := by
  rcases p with ⟨d₁, hd₁, χ₁, hp₁⟩
  rcases q with ⟨d₂, hd₂, χ₂, hp₂⟩
  dsimp at hd hχ
  subst hd
  simp only at hχ
  subst hχ
  rfl

end PrimCharDvd

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]


lemma changeLevel_cast_eq {m d₁ d₂ : ℕ} (heq : d₁ = d₂)
    (hd₂ : d₂ ∣ m) (ψ : DirichletCharacter R d₁) :
    changeLevel hd₂ (heq ▸ ψ) = changeLevel (show d₁ ∣ m from heq ▸ hd₂) ψ := by
  subst heq; rfl


end DirichletCharacter
