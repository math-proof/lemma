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
public import Theorem.Combinatorics.Additive.AP.Basic.Part3

@[expose] public section

variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


/-- The largest size of a subset of `{1, ..., N}` containing no nontrivial `k`-term
arithmetic progression. -/
noncomputable def Set.IsAPOfLengthFree.maxCard (k N : ℕ) : ℕ :=
  by
    classical
    exact Nat.findGreatest
      (fun m ↦ ∃ S : Finset ℕ,
        S ⊆ Finset.Icc 1 N ∧ S.card = m ∧ S.IsAPOfLengthFree k)
      N

