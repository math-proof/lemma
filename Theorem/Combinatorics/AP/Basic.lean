/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AP/Basic.lean -/

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
module

public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Combinatorics.Additive.AP.Three.Defs
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.Set.Card
public import Mathlib.Tactic
public import Def.Combinatorics.AP.Basic

public section

variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


@[simp] theorem Finset.isAPOfLengthFree_coe (s : Finset α) (l : ℕ∞) :
    s.IsAPOfLengthFree l ↔ (s : Set α).IsAPOfLengthFree l :=
  Iff.rfl

