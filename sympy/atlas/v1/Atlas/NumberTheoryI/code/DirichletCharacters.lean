/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletCharacters.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Mathlib.NumberTheory.DirichletCharacter.Basic

abbrev CharacterGroup (G : Type*) [CommGroup G] [Fintype G] := G →* ℂˣ

namespace CharacterGroup

variable {G : Type*} [CommGroup G] [Fintype G]

instance instCommGroup : CommGroup (CharacterGroup G) :=
  inferInstance

instance hasEnoughRootsOfUnity_complex_exponent :
    HasEnoughRootsOfUnity ℂ (Monoid.exponent G) := by
  haveI : NeZero (Monoid.exponent G : ℂ) :=
    ⟨Nat.cast_ne_zero.mpr Monoid.exponent_ne_zero_of_finite⟩
  infer_instance

instance instFinite : Finite (CharacterGroup G) :=
  Finite.of_equiv G
    (CommGroup.monoidHom_mulEquiv_of_hasEnoughRootsOfUnity G ℂ).some.symm.toEquiv

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
