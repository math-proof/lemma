/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Instance.v1.Atlas.NumberTheoryI.code.DirichletCharacters


namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

open DirichletCharacter in
noncomputable def conductorOfDirichletChar {R : Type*} [CommMonoidWithZero R] {n : ℕ}
    (χ : DirichletCharacter R n) : ℕ :=
  χ.conductor

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R] {n : ℕ} (χ : DirichletCharacter R n)

end DirichletCharacter

namespace DirichletCharacter

variable {R : Type*} [CommMonoidWithZero R]

noncomputable def primeSumOver (S : Set Nat.Primes) (s : ℝ) : ℝ :=
  ∑' (p : S), ((p : ℕ) : ℝ) ^ (-s)

noncomputable def primeSumAll (s : ℝ) : ℝ :=
  ∑' (p : Nat.Primes), ((p : ℕ) : ℝ) ^ (-s)

noncomputable def dirichletDensityRatio (S : Set Nat.Primes) (s : ℝ) : ℝ :=
  primeSumOver S s / primeSumAll s

def HasDirichletDensity (S : Set Nat.Primes) (d : ℝ) : Prop :=
  Tendsto (dirichletDensityRatio S) (nhdsWithin 1 (Set.Ioi 1)) (nhds d)

noncomputable def dirichletDensity (S : Set Nat.Primes) : ℝ :=
  (nhdsWithin 1 (Set.Ioi 1)).limUnder (dirichletDensityRatio S)

end DirichletCharacter
end CharacterGroup
