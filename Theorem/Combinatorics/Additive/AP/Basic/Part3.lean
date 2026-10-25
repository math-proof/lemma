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
import Def.Combinatorics.Additive.AP.Basic.Part3
variable {α : Type*} [AddCommMonoid α]

/-! # Arithmetic progressions -/


@[simp] theorem Finset.isAPOfLengthFree_coe (s : Finset α) (l : ℕ∞) :
    s.IsAPOfLengthFree l ↔ (s : Set α).IsAPOfLengthFree l :=
  Iff.rfl

/-- Mathlib's `ThreeAPFree` predicate implies freedom from three-term progressions in the
general-length API. -/
theorem ThreeAPFree.isAPOfLengthFree_three {s : Set ℕ} (hs : ThreeAPFree s) :
    s.IsAPOfLengthFree 3 := by
  intro t hts ht
  rcases ht with ⟨a, d, hcard, rfl⟩
  have ha : a ∈ s := hts ⟨0, by norm_num, by simp⟩
  have hb : a + d ∈ s := hts ⟨1, by norm_num, by simp⟩
  have hc : a + 2 * d ∈ s := hts ⟨2, by norm_num, by simp⟩
  have had : a = a + d := hs ha hb hc (by omega)
  have hd : d = 0 := by omega
  subst d
  have hset :
      {x : ℕ | ∃ n : ℕ, ∃ _ : (n : ℕ∞) < 3, a + n • 0 = x} = {a} := by
    ext x
    constructor
    · rintro ⟨n, hn, rfl⟩
      simp
    · rintro rfl
      exact ⟨0, by norm_num, by simp⟩
  rw [hset] at hcard
  norm_num at hcard

