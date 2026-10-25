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
import Theorem.Combinatorics.Additive.AP.Basic.Part2
variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


/-- A finite set is free of nontrivial arithmetic progressions of length `l`. -/
def Finset.IsAPOfLengthFree (s : Finset α) (l : ℕ∞) : Prop :=
  (s : Set α).IsAPOfLengthFree l

