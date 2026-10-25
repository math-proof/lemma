/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CoveringSystem.lean -/

/-
Copyright 2025 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib.Algebra.Group.Pointwise.Set.Basic
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Int.ModEq
import Mathlib.RingTheory.Ideal.Defs
import Structure.NumberTheory.CoveringSystem
open Pointwise


namespace CoveringSystem

variable {R : Type*} [CommSemiring R]

def coset (c : CoveringSystem R) (i : c.ι) : Set R :=
  {c.residue i} + c.moduli i

end CoveringSystem

namespace Int

def IsCoveringSystem (classes : Finset (ℤ × ℕ)) : Prop :=
  ∀ z : ℤ, ∃ c ∈ classes, Int.ModEq (c.2 : ℤ) z c.1

def indexedCoveringClasses {k : ℕ} (moduli : Fin k → ℕ)
    (residues : Fin k → ℤ) : Finset (ℤ × ℕ) :=
  Finset.univ.image fun i => (residues i, moduli i)

end Int
