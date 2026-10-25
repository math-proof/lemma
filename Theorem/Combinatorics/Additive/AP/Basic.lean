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

import Mathlib.Algebra.Module.NatInt
import Mathlib.Combinatorics.Additive.AP.Three.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Tactic
import Def.Combinatorics.Additive.AP.Basic
variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


namespace Set.IsAPOfLength

variable {s : Set α} {l : ℕ∞}

/-- The cardinality of a set arithmetic progression is its declared length. -/
theorem card (h : s.IsAPOfLength l) : ENat.card s = l :=
  h.choose_spec.choose_spec.1

/-- Unpack a set arithmetic progression into its first term and common difference. -/
theorem eq (h : s.IsAPOfLength l) :
    ∃ a d : α, s = {a + n • d | (n : ℕ) (_ : n < l)} :=
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec.2⟩

end Set.IsAPOfLength
